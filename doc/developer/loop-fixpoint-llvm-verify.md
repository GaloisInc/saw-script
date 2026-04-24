# Design: Loop Fixpoint Support for `llvm_verify`

## Status

**Proposed** — April 2026

## Problem

SAW has three loop-handling mechanisms for symbolic execution of loops with
symbolic bounds:

1. **Simple Loop Fixpoint** — user-supplied Cryptol fixpoint function
2. **Simple Loop Fixpoint CHC** — CHC-based automated fixpoint inference
3. **Simple Loop Invariant** — user-supplied loop invariant

All three are currently gated behind `llvm_verify_x86` only. They cannot be
used with `llvm_verify`, which is the primary verification command for LLVM
bitcode. This means any LLVM bitcode containing loops with symbolic bounds
cannot be verified through the standard `llvm_verify` path.

## Current Architecture

### X86 Path (working)

In `saw-central/src/SAWCentral/Crucible/LLVM/X86.hs`:

```
llvm_verify_x86_common
  ├── fixpointSelect :: FixpointSelect  (line 416)
  │     = NoFixpoint
  │     | SimpleFixpoint TypedTerm
  │     | SimpleFixpointCHC TypedTerm
  │     | SimpleInvariant Text Integer TypedTerm
  │
  ├── Setup fixpoint features (lines 598-624):
  │     case fixpointSelect of
  │       NoFixpoint -> ([], Nothing)
  │       SimpleFixpoint func -> setupSimpleLoopFixpointFeature ...
  │       SimpleFixpointCHC func -> setupSimpleLoopFixpointCHCFeature ...
  │       SimpleInvariant ... -> setupSimpleLoopInvariantFeature ...
  │
  ├── let execFeatures = simpleLoopFixpointFeature ++ psatf
  │
  ├── executeCrucible execFeatures initial  (line 625)
  │
  └── Post-CHC processing (lines 648-657):
        case maybe_ref of
          Just fixpoint_state_ref -> runCHC ...
          Nothing -> (MapF.empty, [])
```

The three setup functions (lines 682-920) produce `ExecutionFeature` values
that the Crucible execution engine uses to handle loops.

### LLVM Verify Path (missing fixpoint support)

In `saw-central/src/SAWCentral/Crucible/LLVM/Builtins.hs`:

```
llvm_verify  (line 289)
  └── verifyMethodSpec  (line 608)
        ├── verifyPrestate  (line 639)
        ├── verifySimulate  (line 651)
        │     ├── withCfgAndBlockId  (line 1556)
        │     ├── Build execFeatures:
        │     │     invariantExecFeatures ++      -- cutpoint-based invariants
        │     │     genericToExecutionFeature pfs  -- profiling features
        │     │     additionalFeatures             -- array size profiling
        │     │     (NO fixpoint features)
        │     ├── executeCrucible execFeatures initExecState  (line 1611)
        │     └── Returns (retval, globals, MapF.empty)  -- always empty invSubst
        └── verifyPoststate  (line 655)
```

Key observation: `verifySimulate` already has infrastructure for execution
features (`execFeatures` list at line 1592) and returns a `MapF` for invariant
substitutions (currently always `MapF.empty`). The plumbing is partially there.

### Underlying Libraries (generic, not x86-specific)

The Crucible libraries that implement loop handling are fully generic:

- `Lang.Crucible.LLVM.SimpleLoopFixpoint` — `simpleLoopFixpoint`
- `Lang.Crucible.LLVM.SimpleLoopFixpointCHC` — `simpleLoopFixpoint`
- `Lang.Crucible.LLVM.SimpleLoopInvariant` — `simpleLoopInvariant`

These produce `ExecutionFeature` values that work with any Crucible execution,
not just x86. The x86 restriction is purely in the SAW command wiring.

## Proposed Changes

### 1. New SAWScript Commands

```
llvm_verify_fixpoint ::
  LLVMModule -> String -> [ProvedSpec] -> Bool ->
  Term ->                    -- fixpoint function
  LLVMCrucibleSetupM () ->
  ProofScript () ->
  TopLevel ProvedSpec

llvm_verify_fixpoint_chc ::
  LLVMModule -> String -> [ProvedSpec] -> Bool ->
  Term ->                    -- fixpoint function
  LLVMCrucibleSetupM () ->
  ProofScript () ->
  TopLevel ProvedSpec
```

These mirror `llvm_verify` but add a fixpoint function parameter.

### 2. Changes to Builtins.hs

#### a. Add imports

```haskell
import qualified Lang.Crucible.LLVM.SimpleLoopFixpoint as Crucible.LLVM.Fixpoint
import qualified Lang.Crucible.LLVM.SimpleLoopFixpointCHC as Crucible.LLVM.FixpointCHC
```

#### b. Add FixpointSelect type (or reuse from X86.hs)

The cleanest approach is to extract `FixpointSelect` and the three `setup*Feature`
functions into a shared module, e.g.,
`SAWCentral.Crucible.LLVM.Fixpoint`:

```haskell
-- New module: SAWCentral.Crucible.LLVM.Fixpoint
module SAWCentral.Crucible.LLVM.Fixpoint
  ( FixpointSelect(..)
  , setupSimpleLoopFixpointFeature
  , setupSimpleLoopFixpointCHCFeature
  ) where
```

Both `X86.hs` and `Builtins.hs` would import from this shared module.

#### c. Modify `verifySimulate` signature

Add a `FixpointSelect` parameter:

```haskell
verifySimulate ::
  ( ... existing constraints ... ) =>
  Options ->
  LLVMCrucibleContext arch ->
  [Crucible.GenericExecutionFeature Sym] ->
  FixpointSelect ->                              -- NEW
  MS.CrucibleMethodSpecIR (LLVM arch) ->
  ...
```

#### d. Wire fixpoint features into `verifySimulate`

Inside `verifySimulate` (around line 1584), after the existing
`invariantExecFeatures` setup:

```haskell
     -- NEW: Set up loop fixpoint features
     (fixpointFeatures, maybe_fixpoint_ref) <-
       case fixpointSel of
         NoFixpoint -> return ([], Nothing)
         SimpleFixpoint func -> do
           let sc = sawCoreSharedContext sym
           sawst <- Common.sawCoreState sym
           f <- setupSimpleLoopFixpointFeature sym sc sawst cfg mvar func
           return ([f], Nothing)
         SimpleFixpointCHC func -> do
           let sc = sawCoreSharedContext sym
           sawst <- Common.sawCoreState sym
           (f, ref) <- setupSimpleLoopFixpointCHCFeature sym sc sawst cfg mvar func
           return ([f], Just ref)

     let execFeatures =
           fixpointFeatures ++          -- NEW
           invariantExecFeatures ++
           map Crucible.genericToExecutionFeature (patSatGenExecFeature ++ pfs) ++
           additionalFeatures
```

#### e. Post-execution CHC processing

After `executeCrucible`, process CHC results (mirroring X86.hs lines 648-657):

```haskell
     -- NEW: Process CHC fixpoint results
     invSubst <- case maybe_fixpoint_ref of
       Just fixpoint_state_ref -> do
         uninterp_inv_fns <-
           Crucible.LLVM.FixpointCHC.executionFeatureContextInvPreds
             <$> readIORef fixpoint_state_ref
         subst <- Crucible.runCHC bak uninterp_inv_fns
         return subst
       Nothing -> return MapF.empty

     -- Return invSubst instead of MapF.empty
     return (retval', globals1, invSubst)
```

#### f. Add new top-level commands

```haskell
llvm_verify_fixpoint ::
  Some LLVMModule -> Text -> [SomeLLVM MS.ProvedSpec] ->
  Bool -> TypedTerm -> LLVMCrucibleSetupM () ->
  ProofScript () -> TopLevel (SomeLLVM MS.ProvedSpec)
llvm_verify_fixpoint (Some lm) nm lemmas checkSat fixpointFn setup tactic =
  do start <- io getCurrentTime
     lemmas' <- checkModuleCompatibility lm lemmas
     withMethodSpec checkSat lm nm setup $ \cc method_spec ->
       do (stats, vcs, _) <-
            verifyMethodSpecWithFixpoint cc method_spec lemmas' checkSat
              (SimpleFixpoint fixpointFn) tactic Nothing
          let lemmaSet = Set.fromList (map (view MS.psSpecIdent) lemmas')
          end <- io getCurrentTime
          let diff = diffUTCTime end start
          ps <- io (MS.mkProvedSpec MS.SpecProved method_spec stats vcs lemmaSet diff)
          returnLLVMProof $ SomeLLVM ps
```

### 3. Accessing `cfg` within `verifySimulate`

A key challenge: `setupSimpleLoopFixpointFeature` requires the `cfg` (Crucible
CFG), which `verifySimulate` already has access to via `withCfgAndBlockId`.
The `cfg` is available inside the callback at line 1556. This means the fixpoint
setup can be done right alongside the existing feature setup.

For `SimpleInvariant`, the x86 path needs a `loopaddr` from symbol resolution
in the ELF file, which doesn't apply to LLVM bitcode. The LLVM bitcode path
would need a different way to identify the loop target. This is the reason
`SimpleInvariant` is harder to port and should be deferred.

### 4. Scope

**Phase 1 (this change):**
- `SimpleFixpoint` — user provides fixpoint function
- `SimpleFixpointCHC` — automated CHC-based inference

**Phase 2 (future):**
- `SimpleInvariant` — requires different loop identification mechanism for
  bitcode (block labels vs. symbol addresses)

## Testing Strategy

1. **Unit test**: Simple C loop (sum 0..n), verify with `llvm_verify_fixpoint`
2. **CHC test**: Same loop with `llvm_verify_fixpoint_chc`
3. **Regression**: Ensure existing `llvm_verify` behavior unchanged when no
   fixpoint is specified
4. **Integration**: Port an existing x86 fixpoint test to use the new LLVM path

Test location: `intTests/test_llvm_loop_fixpoint/`

## Files to Modify

| File | Change |
|------|--------|
| `saw-central/src/SAWCentral/Crucible/LLVM/Builtins.hs` | Add fixpoint imports, modify `verifySimulate`, add new commands |
| `saw-central/src/SAWCentral/Crucible/LLVM/X86.hs` | Extract shared fixpoint setup code |
| `saw-central/src/SAWCentral/Crucible/LLVM/Fixpoint.hs` | **New**: shared fixpoint setup functions |
| `saw/saw-script/src/SAWScript/Interpreter.hs` | Register new `llvm_verify_fixpoint[_chc]` commands |
| `saw.cabal` | Add new module to exposed-modules |

## Risk Assessment

- **Low risk**: The underlying Crucible fixpoint libraries are already generic.
  The change is purely wiring.
- **Medium risk**: The `SimpleFixpoint` setup function (lines 682-750 in X86.hs)
  contains hardcoded assumptions about 64-bit pointer width. This needs
  generalization for the LLVM path which supports 32-bit targets.
- **Low risk**: CHC processing is well-isolated and can be conditionally
  enabled.
