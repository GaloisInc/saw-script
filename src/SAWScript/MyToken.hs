module SAWScript.MyToken where

import AST.hs

data Token p = 
    Identifier { tokPos :: p, tokStr :: String }
  | BitField   { tokPos :: p, tokStr :: String, tokBits :: BitField }
  | Keyword    { tokPos :: p, tokStr :: String }
  | String     { tokPos :: p, tokStr :: String }
  | InfixOp    { tokPos :: p, tokStr :: String }
  | LBrace     { tokPos :: p }
  | RBrace     { tokPos :: p }
  | EOF        { tokPos :: p, tokStr :: String }




(Graphics.Gnuplot.Plot.TwoDimensional.T Interval Prob
, Graphics.Gnuplot.Private.ColorSpecification.T  -> String -> Graphics.Gnuplot.Plot.TwoDimensional.T Interval Prob
,Graphics.Gnuplot.Plot.TwoDimensional.T Interval Prob
,Graphics.Gnuplot.Plot.TwoDimensional.T Prob Interval)'