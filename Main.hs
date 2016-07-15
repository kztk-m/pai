module Main where

import Syntax.Concrete
import Syntax.Abstract
import TreeAutomata.Guided
import Inverter
import Inverter.Action
import Inverter.Build
import Inverter.CodeGen

import Util 

import Control.Monad.State

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe 
import Data.Function (on)
import Data.Char 

import Text.PrettyPrint 
import Debug.Trace

import System.IO
import System.Environment
import System.CPUTime
import Text.Printf

-- import qualified Language.Haskell.TH as TH

import qualified Syntax.MiniHaskell as H 
-- 
-- Main function 
--

main :: IO ()
main = do { args <- getArgs
          ; let conf = parseArgs args defaultConfig
          ; starttime <- getCPUTime
          ; csterr <- case inputFile conf of
                        Nothing -> 
                          do cont <- getContents
                             return $ parseString cont
                        Just filename ->
                             parseFile filename
          ; case csterr of
              Right cprog -> 
               do let (prog, imap, ta, gtaMap, ambi, code) = invert cprog
                  when (debugMode conf) $ debugInfo (prog, ta, gtaMap) 
                  putStrLnE $ showAmbiInfo imap ambi
                  let entries = (show $ head [ f | H.FunD f _   <- code ],
                                 show $ head [ f | Decl _ f _ _ <- decls prog])
                  printCode code (moduleName conf) (extraImport conf) entries
                  printOCode prog 
              Left err -> hPutStrLn stderr (show err)
          ; endtime  <- getCPUTime
          ; when (showElapsedMode conf) (hPrintf stderr "-- %0.2f seconds is elapsed.\n" ( (fromIntegral (endtime - starttime)/(10^12) )::Double ))
          }

showAmbiInfo :: IDMap -> AmbiguityInfo -> [Char]
showAmbiInfo imap Nothing = ""
showAmbiInfo imap (Just (foverlaps, eoverlaps)) = render $
   ptext "--- Ambiguity Info ------------------------------" $$
   ptext "System failed to prove the injectivity because of following reasons: " $$
   vcat (map ppfo foverlaps) $$
   vcat (map ppeo eoverlaps)
  where ppfo (n1,n2) = 
          ptext "Possibly range-overlapping functions: " $$
                    nest 4 (ppr n1 <> comma <> ppr n2)
        ppeo (i1,i2) = 
          ptext "Possibly range-overlapping expressions: " $$
            nest 4 (pprl i1 imap) $$
            nest 4 (pprl i2 imap) 
        pprl e imap =
          case Map.lookup e imap of
            Just (span,str) ->
                let s = startLoc span
                    e = endLoc span
                in if isValidLoc s && isValidLoc e then
                       (ptext "at" <+>
                        parens (hcat [ppr (srcLine s), comma, ppr (srcColumn s)]) <+>
                        ptext "--" <+>
                        parens (hcat [ppr (srcLine e), comma, ppr (srcColumn e)])) $$
                       nest 4 str
                   else
                       ptext "unknown location"
          
putStrLnE = hPutStrLn stderr
                      
data Config 
    = Config 
      { 
        extraImport :: [String],     -- ^ Modules to be imported in the generated code
        inputFile   :: Maybe String, -- ^ Path to input file
        debugMode   :: Bool,         -- ^ Print debug message 
        helpMode    :: Bool,         -- ^ NOT IMPLEMENTED
        showElapsedMode :: Bool,     -- ^ Show Elapsed Time
        moduleName  :: Maybe String -- ^ Module Name for generated code
      }
defaultConfig = Config { 
                  extraImport = [], 
                  inputFile = Nothing, 
                  debugMode = False,
                  helpMode  = False,
                  showElapsedMode = False,
                  moduleName = Nothing }

parseArgs :: [[Char]] -> Config -> Config 
parseArgs args conf =
    case args of 
      ("-i":x:xs) ->
          parseArgs xs (conf { extraImport = x:(extraImport conf) })
      ("-f":x:xs) ->
          parseArgs xs ((makeM x conf) { inputFile = Just x })
      ("-m":x:xs) ->
          parseArgs xs (conf { moduleName = Just x })
      ("-d":xs) ->
          parseArgs xs (conf { debugMode = True })
      ("-h":xs) ->
          parseArgs xs (conf { helpMode  = True })
      ("-t":xs) ->
          parseArgs xs (conf { showElapsedMode = True } )
      (x:xs) | isNothing (inputFile conf) ->
          parseArgs xs ((makeM x conf) { inputFile = Just x })
      (x:xs) ->
          parseArgs xs conf
      [] ->
          conf
    where
      makeM file conf = 
          case moduleName conf of
            Nothing -> conf { moduleName = makeModName file }
            _       -> conf 
      makeModName file =
          let fileName = reverse (takeWhile (/= '/') $ reverse file)
              fileBody = takeWhile (/= '.') fileName 
          in if length fileBody > 0 &&
                all (\x -> isAsciiLower x || isAsciiUpper x || isNumber x) fileBody then
                 Just $ "Inv" ++ fileBody 
             else
                 Nothing
                 
printOCode :: Prog -> IO ()
printOCode prog = 
    putStrLn $ H.pprint (ast2hs prog)


printCode :: [H.Dec] -> Maybe String -> [String] -> (String,String) 
             -> IO ()
printCode code modName imp (e1,e2) 
    = do { putStrLn  "{-# OPTIONS -XNoMonomorphismRestriction #-}"
         ; (case modName of
              Just m  -> putStrLn $ "module " ++ m ++ " (" ++e1++","++e2++") where" 
              Nothing -> return () )
         ; putStrLn  "import Control.Monad"
--         ; putStrLn  "import MyData\n"
         ; putStrLn  "import InvUtil\n"
         ; putStrLn  "import Data.Tuple\n" 
         ; mapM_ putStrLn [ "import " ++ v | v <- imp ]                
         ; putStrLn (H.pprint code ) }


{- for debugging?
afterEps p = render $ ppr $ 
              let (a,b,c) = fromProgramToTA p
              in (eliminateEps a,b,c)
-}
       
-- debugging options

-- debugInfo :: Prog -> IO ()
debugInfo (prog, ta, gta)  =
  do putStrLnE "--- Abstract Syntax Tree ------------------------"
     putStrLnE $ show prog 
     putStrLnE "--- Tree Automata -------------------------------"
     putStrLnE $ render $ ppr $ ta
     putStrLnE "--- Guided Tree Automata ------------------------"
     putStrLnE $ render $ ppr $ gta 
-- was     putStrLnE $ render $ ppr $ testGTA ast 
