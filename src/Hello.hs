module Hello where
import Util (agda2hs)

hello :: IO ()
hello = putStrLn $ "Hello, " ++ agda2hs ++ "!"
