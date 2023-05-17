module Main where

import Sample qualified
import Server qualified

main :: IO Int
main = Server.run