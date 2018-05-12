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

  putStrLn "he left: "
  putStrLn $ print_lower $ left (he 0)

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


  putStrLn "john wonders if everyone admires someone: "
  putStrLn $ print_lower john_wonders_if_everyone_admires_someone

  -- TODO This doesn't expose john as a referent correctly
  putStrLn "john wanted john to be asleep: "
  putStrLn $ print_lower john_wanted_john_to_be_asleep

  putStrLn "john wanted john to be asleep and he is asleep"
  putStrLn $ print_lower conj_sent

  putStrLn "john or keisha admires someone"
  putStrLn $ print_lower disj_sent

  putStrLn "someone is such that john or keisha admires them"
  putStrLn $ print_lower disj_sent3

  putStrLn "john or bill called his mother"
  putStrLn $ print_lower disj_sent2
