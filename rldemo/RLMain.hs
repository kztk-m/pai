module Main where

import MyData
import RUNLENGTH8

import Data.Bits
import qualified Data.ByteString as B

import Control.Monad

import System.Environment
import System.Exit

import Data.Word 

w2bl :: Word8 -> List B 
w2bl w = 
    fromHsList $ trunc $ map h $ map (testBit w) [0..7]
        where h True  = B1
              h False = B0
              trunc x    = reverse $ f $ reverse x 
                  where
                    f (B0:x) = f x
                    f y      = y 

bl2w :: List B -> Word8 
bl2w bl = 
    foldr (\(a,i) r -> 
               case a of
                 B1 -> 
                     r `setBit` i 
                 B0 -> 
                     r) 0 $ zip (toHsList bl) [0..7]


fromBS = fromHsList . map w2bl .  B.unpack 
toBS   = B.pack . map bl2w . toHsList 

rlEnc :: B.ByteString -> B.ByteString
rlEnc =
    toBS . runlength . fromBS

rlDec :: B.ByteString -> B.ByteString
rlDec = 
    toBS . inv_Frunlength . fromBS

convertBy f src dst =
    do bs <- B.readFile src
       B.writeFile dst (f bs)

main = 
    do { args <- getArgs
       ; when (length args < 3) 
              (printHelp >> exitSuccess)
       ; case args of 
           (e:src:dst:_) | isEnc(e) -> 
               convertBy rlEnc src dst
           (d:src:dst:_) | isDec(d) ->
               convertBy rlDec src dst}
    where
      isEnc ('e':_) = True
      isEnc ('E':_) = True
      isEnc _       = False
      isDec ('d':_) = True
      isDec ('D':_) = True
      isDec _       = False
    

printHelp =
    do p <- getProgName 
       putStrLn $ p ++ " " ++ "(decode|encode) INPUT_FILE OUTPUT_FILE"