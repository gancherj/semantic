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

  putStrLn "he left and do did everyone: "
  putStrLn $ print_lower $ conj (left (he 0)) (so_does everyone)

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

  -- TODO this gives the wrong reading, because each BDI forms a separate verb.
  putStrLn "john wonders if everyone admires someone and so does keisha: "
  putStrLn $ print_lower $ conj john_wonders_if_everyone_admires_someone (so_does keisha)

  putStrLn "john wanted john to be asleep: "
  putStrLn $ print_lower john_wanted_john_to_be_asleep

  putStrLn "john wanted john to be asleep and he is asleep and so is everyone"
  putStrLn $ print_lower $ conj conj_sent (so_does everyone)

  putStrLn "john or keisha admires someone"
  putStrLn $ print_lower disj_sent

  putStrLn "someone is such that john or keisha admires them"
  putStrLn $ print_lower disj_sent3

  putStrLn "john or bill called his mother"
  putStrLn $ print_lower disj_sent2

  putStrLn "so does everyone"
  putStrLn $ print_lower $ so_does everyone

  putStrLn "john wants to be an actor"
  putStrLn $ print_lower $ john_wants_actor

  putStrLn "john wants to be an actor and so does keisha"
  putStrLn $ print_lower $ conj john_wants_actor (so_does keisha)
