//! This tests `crux-mir-comp` verification involving zero-sized enums along
//! many of the same axes as `intTests/test_mir_verify_zst_enums/test.rs`.

extern crate crucible;
extern crate crucible_proc_macros;

use crucible::*;
use crucible_proc_macros::*;

#[derive(Clone, Copy, Symbolic)]
enum E1 {
    A(()),
}

#[derive(Clone, Copy, Symbolic)]
#[repr(transparent)]
enum E2 {
    A(()),
}

fn f1(e: &E1) {
    match e {
        E1::A(u) => *u,
    }
}

#[crux_spec_for(f1)]
fn f1_equiv() {
    let e = E1::symbolic("e");
    let expected = ();
    let actual = f1(&e);
    crucible_assert!(expected == actual);
}

fn f2(e: &E2) {
    match e {
        E2::A(u) => *u,
    }
}

#[crux_spec_for(f2)]
fn f2_equiv() {
    let e = E2::symbolic("e");
    let expected = ();
    let actual = f2(&e);
    crucible_assert!(expected == actual);
}

fn g1(e: E1) {
    f1(&e)
}

#[crux_spec_for(g1)]
fn g1_equiv() {
    f1_equiv_spec().enable();

    let e = E1::symbolic("e");
    let expected = ();
    let actual = g1(e);
    crucible_assert!(expected == actual);
}

fn g2(e: E2) {
    f2(&e)
}

#[crux_spec_for(g2)]
fn g2_equiv() {
    f2_equiv_spec().enable();

    let e = E2::symbolic("e");
    let expected = ();
    let actual = g2(e);
    crucible_assert!(expected == actual);
}

fn h1(e: E1) {
    g1(e)
}

#[crux_spec_for(h1)]
fn h1_equiv() {
    g1_equiv_spec().enable();

    let e = E1::symbolic("e");
    let expected = ();
    let actual = h1(e);
    crucible_assert!(expected == actual);
}

fn h2(e: E2) {
    g2(e)
}

#[crux_spec_for(h2)]
fn h2_equiv() {
    g2_equiv_spec().enable();

    let e = E2::symbolic("e");
    let expected = ();
    let actual = h2(e);
    crucible_assert!(expected == actual);
}
