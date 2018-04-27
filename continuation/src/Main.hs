-- TODO: finish the "knows" example.

module Main where
import Lang
import Examples

  
main :: IO ()
main = do

  putStrLn "everyone left: "
  putStrLn $ print_lower everyone_left

  putStrLn "john left: "
  putStrLn $ print_lower john_left

  putStrLn "john admires everyone: "
  putStrLn $ print_lower john_admires_everyone

  putStrLn "everyone admires everyone: "
  putStrLn $ print_lower everyone_admires_everyone

  putStrLn "everyone admires someone: "
  putStrLn $ print_lower everyone_admires_someone

  putStrLn "someone admires someone: "
  putStrLn $ print_lower someone_admires_someone

  putStrLn "someone admires everyone: "
  putStrLn $ print_lower someone_admires_everyone

  putStrLn "john wonders if True: "
  putStrLn $ print_lower john_wonders_if_true


  -- TODO is this the correct reading? 
  putStrLn "john wonders if everyone admires someone: "
  putStrLn $ print_lower john_wonders_if_everyone_admires_someone

  putStrLn "john wanted john to be asleep: "
  putStrLn $ print_lower john_wanted_john_to_be_asleep

