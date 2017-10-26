module GrammarC where

import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Char
import qualified Data.Set as S

import Debug.Trace

import qualified PGF2
import qualified PGF2.Internal as I

--------------------------------------------------------------------------------
-- grammar types

-- name

type Name = String
type Cat  = PGF2.Cat -- i.e. String

-- concrete category

data ConcrCat = CC (Maybe Cat) I.FId -- i.e. Int
  deriving ( Ord, Eq )

instance Show ConcrCat where
  show (CC (Just cat) fid) = cat ++ "_" ++ show fid 
  show (CC Nothing fid)    = "_" ++ show fid 


-- tree

data Tree
  = App{ top :: Symbol, args :: [Tree] }
 deriving ( Eq, Ord )

-- symbol

data Symbol
  = Symbol
  { name :: Name
  , typ  :: ([Cat], Cat)
  }
 deriving ( Eq, Ord )

-- grammar

data Grammar
  = Grammar
  { parse        :: String -> [Tree]
  , linearize    :: Tree -> String
  , linearizeAll :: Tree -> [String]
  , tabularLin   :: Tree -> [(String,String)]
  , concrCats    :: [(PGF2.Cat,I.FId,I.FId,[String])]
  , productions  :: I.FId -> [I.Production] --just for debugging
  , linFunctions :: [(PGF2.Fun,[ConcrCat],ConcrCat)]
  , startCat     :: Cat
  , symbols      :: [Symbol]
  , feat         :: FEAT
  }

--------------------------------------------------------------------------------
-- name

mkName, mkCat :: String -> Name
mkName = id
mkCat  = id

-- tree

instance Show Tree where
  show = showTree

showTree :: Tree -> String
showTree (App a []) = show a
showTree (App f xs) = unwords (show f : map showTreeArg xs)
  where showTreeArg (App a []) = show a
        showTreeArg t = "(" ++ showTree t ++ ")"

catOf :: Tree -> Cat
catOf (App f _) = snd (typ f)

-- symbol

instance Show Symbol where
  show f = name f --CId is just a String in PGF2

-- grammar

toGrammar :: PGF2.PGF -> Grammar
toGrammar pgf =
  let gr =
        Grammar
        { parse = \s ->
            case PGF2.parse lang (PGF2.startCat pgf) s of 
              PGF2.ParseOk es_fs -> map (mkTree.fst) es_fs
              PGF2.ParseFailed i s -> error s
              PGF2.ParseIncomplete -> error "Incomplete parse"

        , linearize = \t ->
            PGF2.linearize lang (mkExpr t)

        , linearizeAll = \t -> 
            PGF2.linearizeAll lang (mkExpr t)

        , tabularLin = \t ->
            PGF2.tabularLinearize lang (mkExpr t)

        , startCat =
            mkCat (PGF2.startCat pgf)

        , concrCats = I.concrCategories lang

        , productions = \fid -> I.concrProductions lang fid

        , linFunctions = 
           [ ( fst (I.concrFunction lang funId)
             , [ CC cat fid | I.PArg _ fid <- pargs 
                            , cat <- getGFCat fid ]
             , CC resCat resFid) 
                  | (cat,bg,end,_) <- concrCats gr 
                  , resFid <- [bg..end] 
                  , prod <- I.concrProductions lang resFid 
                  , (funId,_,pargs) <- getCFun prod 
                  , resCat <- getGFCat resFid
                  ]


        , symbols =
            [ mkSymbol f
            | f <- PGF2.functions pgf
            , Just _ <- [PGF2.functionType pgf f]
            ]

        , feat =
            mkFEAT gr
        }
   in gr
 where

  lang = snd $ head $ Map.assocs $ PGF2.languages pgf  
  
  -- a FId may be a coercion for multiple categories, hence []
  -- a FId may not be found at all (why?), hence Maybe
  -- In the latter case, just insert the Nothing directly into ConcrCat.
  getGFCat :: I.FId -> [Maybe Cat]
  getGFCat fid = 
    let coercedFids = [ cfid | prod <- I.concrProductions lang fid
                             , let cfid = case prod of
                                           I.PCoerce cf -> cf
                                           I.PApply _ _ -> fid ]

        cats = nub [ cat | (cat,bg,end,xs) <- I.concrCategories lang
                         , cfid <- coercedFids
                         , cfid `elem` [bg..end] ] 
     in case cats of 
          [] -> [Nothing]
          xs -> map Just xs

  getCFun :: I.Production -> [(I.FunId,PGF2.Fun,[I.PArg])]
  getCFun cprod = case cprod of
    I.PApply funId pargs -> [(funId,fst $ I.concrFunction lang funId,pargs)]
    I.PCoerce concrCat   -> concatMap getCFun (I.concrProductions lang concrCat)

  mkSymbol f = Symbol f ([mkCat x | (_,_,x) <- xs],y)
   where
    Just ft    = PGF2.functionType pgf f -- functionType :: PGF -> Fun -> Maybe Type
    (xs, y, _) = PGF2.unType ft
   
  mkTree t =
   case PGF2.unApp t of
     Just (f,xs) -> App (mkSymbol f) [ mkTree x | x <- xs ]
     _           -> error (PGF2.showExpr [] t)
  
  mkExpr (App n []) | not (null s) && all isDigit s =
    PGF2.mkInt (read s)
   where
    s = show n

  mkExpr (App f xs) =
    PGF2.mkApp (name f) [ mkExpr x | x <- xs ]
  
  mkCat  tp  = cat where (_, cat, _) = PGF2.unType tp
  mkType cat = PGF2.mkType [] cat []

readGrammar :: FilePath -> IO Grammar
readGrammar file =
  do pgf <- PGF2.readPGF file
     return (toGrammar pgf)

-- FEAT-style generator magic

type FEAT = Cat -> Int -> (Integer, Integer -> Tree)

-- compute how many trees there are of a given size and type
featCard :: Grammar -> Cat -> Int -> Integer
featCard gr c n = fst (feat gr c n)

-- generate the i-th tree of a given size and type
featIth :: Grammar -> Cat -> Int -> Integer -> Tree
featIth gr c n i = snd (feat gr c n) i

mkFEAT :: Grammar -> FEAT
mkFEAT gr =
  \c s -> let (n,h) = catList [c] s in (n, head . h)
 where
  catList' [] s =
    if s == 0
      then (1, \0 -> [])
      else (0, error "empty")

  catList' [c] s =
    parts [ (n, \i -> [App f (h i)])
          | s > 0 
          , f <- symbols gr
          , let (xs,y) = typ f
          , y == c
          , let (n,h) = catList xs (s-1)
          ]

  catList' (c:cs) s =
    parts [ (nx*nxs, \i -> hx (i `mod` nx) ++ hxs (i `div` nx))
          | k <- [0..s]
          , let (nx,hx)   = catList [c] k
                (nxs,hxs) = catList cs (s-k)
          ]

  catList = memo catList'
   where
    cats = nub [ x | f <- symbols gr, let (xs,y) = typ f, x <- y:xs ]

    memo f = \cs -> case cs of
                      []   -> (nil !!)
                      a:as -> head [ f' as | (c,f') <- cons, a == c ]
     where
      nil  = [ f [] s | s <- [0..] ]
      cons = [ (c, memo (f . (c:))) | c <- cats ]

  parts []          = (0, error "empty parts ")
  parts ((n,h):nhs) = (n+n', \i -> if i < n then h i else h' (i-n))
   where
    (n',h') = parts nhs

--------------------------------------------------------------------------------
