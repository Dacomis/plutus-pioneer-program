main :: IO ()
main = bar -- putStrLn "Hello, world!"

bar :: IO ()
bar =
  getLine >>= \s ->
    getLine >>= \t ->
      putStrLn (s ++ t)