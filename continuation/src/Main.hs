-- TODO: finish the "knows" example.

module Main where
import Lang

  
main :: IO ()
main = do

  putStrLn $ show $ simpl $ toExp everyone_left
  putStrLn $ show $ simpl $ toExp everyone_left2
