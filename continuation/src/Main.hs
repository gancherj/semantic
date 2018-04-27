-- TODO: finish the "knows" example.

module Main where
import Lang
import Examples

  
main :: IO ()
main = do

  putStrLn "everyone left: "
  putStrLn $ show $ simpl $ toExp everyone_left

  putStrLn "john left: "
  putStrLn $ show $ simpl $ toExp john_left

  putStrLn "john admires everyone: "
  putStrLn $ show $ simpl $ toExp john_admires_everyone

  putStrLn "everyone admires everyone: "
  putStrLn $ show $ simpl $ toExp everyone_admires_everyone

  putStrLn "everyone admires someone: "
  putStrLn $ show $ simpl $ toExp everyone_admires_someone

  putStrLn "someone admires someone: "
  putStrLn $ show $ simpl $ toExp someone_admires_someone

  putStrLn "someone admires everyone: "
  putStrLn $ show $ simpl $ toExp someone_admires_everyone

