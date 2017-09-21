module Grammar where

import Data.List
import Data.Maybe
import Data.Char
import qualified Data.Set as S

import qualified PGF
import PGF( CId, mkCId )

--------------------------------------------------------------------------------
-- grammar types

-- name

type Name = CId
type Cat  = CId

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
  , startCat     :: Cat
  , symbols      :: [Symbol]
  , sizes        :: Sizes
  }

--------------------------------------------------------------------------------
-- name

mkName, mkCat :: String -> Name
mkName = mkCId
mkCat  = mkCId

-- tree

instance Show Tree where
  show (App a []) = show a
  show (App f xs) =  show f ++ "(" ++ concat (intersperse "," (map show xs)) ++ ")"

showTree :: Tree -> String
showTree (App a []) = show a
showTree (App f xs) = unwords (show f : map showTreeArg xs)
  where showTreeArg (App a []) = show a
        showTreeArg t = " ( " ++ showTree t ++ " ) "

catOf :: Tree -> Cat
catOf (App f _) = snd (typ f)

-- symbol

instance Show Symbol where
  show f = PGF.showCId (name f) 

-- grammar

toGrammar :: PGF.PGF -> Grammar
toGrammar pgf =
  let gr =
        Grammar
        { parse = \s ->
            [ mkTree t
            | t <- PGF.parse pgf lang (PGF.startCat pgf) s
            ]
  
        , linearize = \t ->
            PGF.linearize pgf lang (mkExpr t)

        , linearizeAll = \t -> 
            PGF.linearizeAll pgf (mkExpr t)

        , startCat =
            mkCat (PGF.startCat pgf)
  
        , symbols =
            [ mkSymbol f
            | f <- PGF.functions pgf
            , Just _ <- [PGF.functionType pgf f]
            ]

        , sizes =
            mkSizes gr
        }
   in gr
 where
  lang = head $ PGF.languages pgf  
  
  mkSymbol f = Symbol f ([mkCat x | (_,_,x) <- xs],y)
   where
    Just ft    = PGF.functionType pgf f
    (xs, y, _) = PGF.unType ft
   
  mkTree t =
   case PGF.unApp t of
     Just (f,xs) -> App (mkSymbol f) [ mkTree x | x <- xs ]
     _           -> error (PGF.showExpr [] t)
  
  mkExpr (App n []) | not (null s) && all isDigit s =
    PGF.mkInt (read s)
   where
    s = show n

  mkExpr (App f xs) =
    PGF.mkApp (name f) [ mkExpr x | x <- xs ]
  
  mkCat  tp  = cat where (_, cat, _) = PGF.unType tp
  mkType cat = PGF.mkType [] cat []

readGrammar :: FilePath -> IO Grammar
readGrammar file =
  do pgf <- PGF.readPGF file
     return (toGrammar pgf)

-- FEAT-style generator magic

type Sizes = Cat -> Int -> (Integer, Integer -> Tree)

mkSizes :: Grammar -> Sizes
mkSizes gr =
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

