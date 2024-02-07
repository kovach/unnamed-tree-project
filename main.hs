{-# LANGUAGE ExistentialQuantification, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{- This file contains a start toward a functional specification of traversal algorithms
 - for augmented trees (especially trees augmented with geometric data).
 -}

-- Basic "stream fusion" definition
data Step s k v
  = Done
  | Skip k s
  | Emit k v s
  -- used for branching on value of k
  | Group k s s

data Stream k v = forall s. Stream s (s -> Step s k v)

listStream :: [a] -> Stream Int a
listStream xs = Stream (0, xs) next
  where
    next (_, []) = Done
    next (i, (a : as)) = Emit i a (i+1, as)

eval :: Stream k a -> [a]
eval (Stream q next) =
  case next q of
    Done         -> []
    Skip _ q'    -> eval (Stream q' next)
    Emit _ v q'  -> v : eval (Stream q' next)
    Group k q q' -> eval (Stream q next)

foldS :: (b -> a -> b) -> b -> Stream k a -> b
foldS f acc (Stream q next) =
  case next q of
    Done        -> acc
    Skip _ q'   -> foldS f acc (Stream q' next)
    Emit _ v q' -> foldS f (f acc v) (Stream q' next)
    Group _ q _ -> foldS f acc (Stream q next)

-- for testing
foldS' :: (b -> a -> b) -> (b -> k -> b) -> b -> Stream k a -> b
foldS' f g acc (Stream q next) =
  case next q of
    Done        -> acc
    Skip k q'   -> foldS' f g (g acc k) (Stream q' next)
    Emit _ v q' -> foldS' f g (f acc v) (Stream q' next)
    Group _ q _ -> foldS' f g acc (Stream q next)

filterS f (Stream q next) = Stream q next'
  where
    next' s = case next s of
      Done -> Done
      Skip k q' -> Skip k q'
      Emit k v q' -> if f k then Emit k v q' else Skip k q'
      Group k true false -> if f k then Skip k true else Skip k false

-- The tree definition and helper code is adapted from https://apfelmus.nfshost.com/articles/monoid-fingertree.html
--   todo: investigate this post and the finger tree paper further
data Tree v a
  = Leaf v a
  | Branch v (Tree v a) (Tree v a)
  deriving Show

tag (Leaf v _) = v
tag (Branch v _ _) = v

class Semigroup v => Measured a v where
  measure :: a -> v

instance Semigroup a => Measured a a where
  measure = id

leaf x = Leaf (measure x) x

branch :: Semigroup v => Tree v a -> Tree v a -> Tree v a
branch x y = Branch (tag x <> tag y) x y

-- traverse tree as stream
ts :: Tree k a -> Stream k a
ts t = Stream [t] next
  where
    -- important (?) variant: the union of all the shapes on the stack
    --   this variant decreases monotonically over time
    next [] = Done
    next (Leaf i v : k) = Emit i v k
    next (Branch i a b : k) = Group i (a:b:k) k

-- left to right leaf traversal
listTree :: Tree v a -> [a]
listTree = eval . ts

{- Examples -}
instance Semigroup Int where (<>) = (+)

-- example geometric query: interval contains point?
data Interval = Interval { lo :: Int , hi :: Int }

ii :: Int -> Int -> Tree Interval Interval
ii x y = leaf (Interval x y)

instance Show Interval where
  show (Interval lo hi) = "[" ++ show lo ++ "-" ++ show hi ++ "]"

type Pt = Int

mem :: Pt -> Interval -> Bool
mem (pt) i = lo i <= pt && pt <= hi i

instance Semigroup Interval where
  x <> y = Interval { lo = min (lo x) (lo y), hi = max (hi x) (hi y) }

t1 :: Tree Int Int
t1 = (branch (leaf 2) (branch (leaf 3) (leaf 7)))
eg1 = tfold (+) 0 t1 [] -- 12

chk = eval . filterS (mem 1) . ts
count = foldS (\a _ -> a+1) 0

-- t2 = ([0-2] ([1-3] [2-4]))
t2 = branch (ii 0 2) (branch (ii 1 3) (ii 2 4))

-- basic demo:
--   countSkip filters a tree and computes the list of nodes where Skip is returned
countSkip i = reverse .
  foldS' (\a _ -> a) (\acc k -> k : acc) [] .
  filterS (mem i) .
  ts
main = do
  print $ countSkip 5 t2 -- skips 1 times (root)
  print $ countSkip 0 t2 -- skips 2 times (root, whole right subtree)
  print $ countSkip 1 t2 -- skips 3 times (root, right node, rightmost node)
  print $ countSkip 3 t2 -- skips 3 times (root, left node, right node)

-- junk for later:

-- for reference
tfold f x (Leaf _ x') [] = f x x'
tfold f x (Leaf _ x') ((_, r) : k) = tfold f (f x x') r k
tfold f x (Branch label a b) k = tfold f x a ((label, b) : k)

data Zipper v a
  = Root
  | BranchL v (Tree v a) (Zipper v a) -- right
  | BranchR v (Tree v a) (Zipper v a) -- left

instance (Measured a b, Measured a c) => Measured a (b, c) where
  measure x = (measure x, measure x)

