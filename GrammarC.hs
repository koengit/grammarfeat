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
  , ctyp :: [([ConcrCat],ConcrCat)] --There's a bug: this is supposed to be all the concrcats, but it's actually only one, and symbols contains a duplicate symbol for each concrcat!
  }
 deriving ( Eq, Ord )

mergeSymb :: Symbol -> Symbol -> Symbol
mergeSymb s1 s2 = s1 { ctyp = ctyp s1 ++ ctyp s2 }

symbEq s1 s2 = name s1 == name s2
               

-- grammar

data Grammar
  = Grammar
  { parse        :: String -> [Tree]
  , linearize    :: Tree -> String
  , linearizeAll :: Tree -> [String]
  , tabularLin   :: Tree -> [(String,String)]
  , concrCats    :: [(PGF2.Cat,I.FId,I.FId,[String])]
--  , productions  :: I.FId -> [I.Production] --just for debugging
  , coercions    :: [(ConcrCat,ConcrCat)]
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

        , symbols = 
           [ Symbol { name = fst $ I.concrFunction lang funId ,
                      ctyp = ctypes ,
                      typ = head [ (map abstrCat argCats,abstrCat resCat)
                                   | (argCats,resCat) <- ctypes ] }

                  | (cat,bg,end,_) <- concrCats gr 
                  , resFid <- [bg..end] 
                  , I.PApply funId pargs <- I.concrProductions lang resFid
                  , let ctypes 
                         = [ ( [ CC argCat fid | I.PArg _ fid <- pargs 
                                               , argCat <- getGFCat fid ]
                             ,  CC resCat resFid) 
                            | resCat <- getGFCat resFid ]
                  ]

        , coercions = coerces

        , feat =
            mkFEAT gr
        }
   in gr
 where
  lang = snd $ head $ Map.assocs $ PGF2.languages pgf  

  coerces = [ ( CC Nothing afid
               , CC ccat cfid )
              | afid <- [0..I.concrTotalCats lang]
              , I.PCoerce cfid  <- I.concrProductions lang afid 
              , ccat <- getGFCat cfid ]


  abstrCat :: ConcrCat -> Cat
  abstrCat c@(CC Nothing _)  = let Just ccat = lookup c coerces 
                                in abstrCat ccat
  abstrCat (CC (Just cat) _) = cat
  
  -- a FId may be a coercion for multiple categories, hence []
  -- The result of this function is inserted into ConcrCat,
  -- where Just means not a coercion and Nothing means coercion.
  -- But coercions are taken care of here, so if we get [Nothing],
  -- it seems like something is wrong? (trace to find out if that happens)
  getGFCat :: I.FId -> [Maybe Cat]
  getGFCat fid = 
    let coercedFids = [ cfid | prod <- I.concrProductions lang fid
                             , let cfid = case prod of
                                           I.PCoerce cf -> cf
                                           I.PApply _ _ -> fid ]

        cats = nub [ cat | (cat,bg,end,xs) <- I.concrCategories lang
                         , fid `elem` [bg..end] ]
                         --, cfid <- coercedFids
                         --, cfid `elem` [bg..end] ] 
     in case cats of 
          [] -> --trace ("getGFCat: no values for fID " ++ show fid) $ 
                [Nothing]
          xs -> map Just xs

  --getCFun :: I.Production -> [(I.FunId,PGF2.Fun,[I.PArg])]
  --getCFun cprod = case cprod of
  --  I.PApply funId pargs -> [(funId,fst $ I.concrFunction lang funId,pargs)]
  --  I.PCoerce concrCat   -> concatMap getCFun (I.concrProductions lang concrCat)


  mkSymbol f = Symbol f ([mkCat x | (_,_,x) <- xs],y) []
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

type FEAT = [ConcrCat] -> Int -> (Integer, Integer -> [Tree])

-- compute how many trees there are of a given size and type
featCard :: Grammar -> ConcrCat -> Int -> Integer
featCard gr c n = featCardVec gr [c] n

-- generate the i-th tree of a given size and type
featIth :: Grammar -> ConcrCat -> Int -> Integer -> Tree
featIth gr c n i = head (featIthVec gr [c] n i)

-- compute how many tree-vectors there are of a given size and type-vector
featCardVec :: Grammar -> [ConcrCat] -> Int -> Integer
featCardVec gr cs n = fst (feat gr cs n)

-- generate the i-th tree-vector of a given size and type-vector
featIthVec :: Grammar -> [ConcrCat] -> Int -> Integer -> [Tree]
featIthVec gr cs n i = snd (feat gr cs n) i

mkFEAT :: Grammar -> FEAT
mkFEAT gr = catList
 where
  catList' [] s =
    if s == 0
      then (1, \0 -> [])
      else (0, error "empty")

  catList' [c] s =
    parts $ 
          [ (n, \i -> [App f (h i)])
          | s > 0 
          , f <- symbols gr
          , (xs,y) <- ctyp f
          , y == c
          , let (n,h) = catList xs (s-1)
          ] ++
          [ catList [x] s -- put (s-1) if it doesn't terminate
          | s > 0 
          , (x,y) <- coercions gr
          , y == c
          ] 

  catList' (c:cs) s =
    parts [ (nx*nxs, \i -> hx (i `mod` nx) ++ hxs (i `div` nx))
          | k <- [0..s]
          , let (nx,hx)   = catList [c] k
                (nxs,hxs) = catList cs (s-k)
          ]

  catList = memo catList'
   where
    cats = nub $ [ x | f <- symbols gr
                   , (xs,y) <- ctyp f
                   , x <- y:xs ] ++
                 [ z | (x,y) <- coercions gr
                     , z <- [x,y] ] --adds all possible categories in the grammar
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
