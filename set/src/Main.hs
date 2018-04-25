-- TODO: finish the "knows" example.

module Main where
import Lang

  
main :: IO ()
main = do

  putStrLn $ show $ sent2
  putStrLn " "
  putStrLn $ show $ simpl sent2
  putStrLn " "
  putStrLn $ show $ simpl sent3
