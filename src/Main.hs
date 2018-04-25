-- TODO: finish the "knows" example.

module Main where
import Lang

  
main :: IO ()
main = do
  putStrLn $ ppExp sent []
  putStrLn $ show $ simpl sent
