{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWScript.REPL.Logo
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.REPL.Logo where

import SAWScript.Panic (panic)
import SAWVersion.Version (versionText)
import System.Console.ANSI

type Version = String

type Logo = [String]

logo :: Bool -> Logo
logo useColor =
     [ sgr [SetColor Foreground Dull  White] ++ l | l <- ws ]
  ++ [ sgr [SetColor Foreground Vivid Blue ] ++ l | l <- vs ]
  ++ [ sgr [SetColor Foreground Dull  Blue ] ++ l | l <- ds ]
  ++ [ sgr [Reset] ]
  where
  sgr | useColor  = setSGRCode
      | otherwise = const []
  ver = sgr [SetColor Foreground Dull White]
        ++ replicate (lineLen - 20 - length versionText) ' '
        ++ versionText
  ls = (if useColor then logo2 else logo1) ver
  line      = case ls of
                line':_ -> line'
                [] -> panic "logo" ["empty lines"]
  lineLen   = length line
  slen      = length ls `div` 3
  (ws,rest) = splitAt slen ls
  (vs,ds)   = splitAt slen rest

logo1 :: String -> [String]
logo1 ver =
    [ "   ___  __ _ _ _ _"
    , "  / __|/ _\' | | | |"
    , "  \\__ \\ (_| | | | |"
    , "  |___/\\__,_|\\_,_/ " ++ ver
    ]

logo2 :: String -> [String]
logo2 ver =
    [ " ┏━━━┓━━━┓━┓━┓━┓"
    , " ┃ ━━┓ ╻ ┃ ┃ ┃ ┃"
    , " ┣━━ ┃ ╻ ┃┓ ╻ ┏┛"
    , " ┗━━━┛━┛━┛┗━┛━┛ " ++ ver
    ]

displayLogo :: Bool -> IO ()
displayLogo useColor = mapM_ putStrLn (logo useColor)
