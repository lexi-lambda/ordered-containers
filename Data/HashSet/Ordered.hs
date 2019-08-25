{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- | An 'OHashSet' behaves much like a 'HashSet', with mostly the same asymptotics, but
-- also remembers the order that values were inserted. All operations whose
-- asymptotics are worse than 'HashSet' have documentation saying so.
-- @since 0.3
module Data.HashSet.Ordered
	( OHashSet
	-- * Trivial sets
	, empty, singleton
	-- * Insertion
	-- | Conventions:
	--
	-- * The open side of an angle bracket points to an 'OHashSet'
	--
	-- * The pipe appears on the side whose indices take precedence for keys that appear on both sides
	--
	-- * The left argument's indices are lower than the right argument's indices
	, (<|), (|<), (>|), (|>)
	, (<>|), (|<>)
	, Bias(Bias, unbiased), L, R
	-- * Query
	, null, size, member
	-- * Deletion
	, delete, filter, (\\), (|/\), (/\|)
	-- * Indexing
	, Index, findIndex, elemAt
	-- * List conversion
	, fromList
#if MIN_VERSION_unordered_containers(0,2,10)
	-- * 'HashSet' conversion
	, toHashSet
#endif
	) where

import Control.Monad (guard)
import Data.Data
import Data.Foldable (Foldable, foldl', foldMap, foldr, toList)
import Data.Function (on)
import Data.Hashable (Hashable(..))
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.Map.Strict (Map)
import Data.Map.Util
import Data.Monoid (Monoid(..))
#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif
import Prelude hiding (filter, foldr, lookup, null)
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as HM
import qualified GHC.Exts as Exts

data OHashSet a = OHashSet !(HashMap a Tag) !(Map Tag a)
	deriving Typeable

-- | Values appear in insertion order, not ascending order.
instance Foldable OHashSet where foldMap f (OHashSet _ vs) = foldMap f vs
instance Eq   a => Eq   (OHashSet a) where (==)    = (==)    `on` toList
instance Ord  a => Ord  (OHashSet a) where compare = compare `on` toList
instance Show a => Show (OHashSet a) where showsPrec = showsPrecList toList
instance (Eq a, Hashable a, Read a) => Read (OHashSet a) where readsPrec = readsPrecList fromList
instance Hashable a => Hashable (OHashSet a) where hashWithSalt s = hashWithSalt s . toList

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.
instance (Data a, Eq a, Hashable a) => Data (OHashSet a) where
	gfoldl f z set = z fromList `f` toList set
	toConstr _     = fromListConstr
	gunfold k z c  = case constrIndex c of
		1 -> k (z fromList)
		_ -> error "gunfold"
	dataTypeOf _   = oHashSetDataType
	-- dataCast1 /must/ be eta-expanded in order to build on GHC 7.8.
	dataCast1 f    = gcast1 f

fromListConstr :: Constr
fromListConstr = mkConstr oHashSetDataType "fromList" [] Prefix

oHashSetDataType :: DataType
oHashSetDataType = mkDataType "Data.HashSet.Ordered.Set" [fromListConstr]

-- | @'GHC.Exts.fromList' = 'fromList'@ and @'GHC.Exts.toList' = 'toList'@.
instance (Eq a, Hashable a) => Exts.IsList (OHashSet a) where
	type Item (OHashSet a) = a
	fromList = fromList
	toList = toList

#if MIN_VERSION_base(4,9,0)
instance (Eq a, Hashable a) => Semigroup (Bias L (OHashSet a)) where Bias o <> Bias o' = Bias (o |<> o')
instance (Eq a, Hashable a) => Semigroup (Bias R (OHashSet a)) where Bias o <> Bias o' = Bias (o <>| o')
#endif

-- | Empty sets and set union. When combining two sets that share elements, the
-- indices of the left argument are preferred.
--
-- See the asymptotics of ('|<>').
instance (Eq a, Hashable a) => Monoid (Bias L (OHashSet a)) where
	mempty = Bias empty
	mappend (Bias o) (Bias o') = Bias (o |<> o')

-- | Empty sets and set union. When combining two sets that share elements, the
-- indices of the right argument are preferred.
--
-- See the asymptotics of ('<>|').
instance (Eq a, Hashable a) => Monoid (Bias R (OHashSet a)) where
	mempty = Bias empty
	mappend (Bias o) (Bias o') = Bias (o <>| o')

infixr 5 <|, |<   -- copy :
infixl 5 >|, |>
infixr 6 <>|, |<> -- copy <>

(<|), (|<) :: (Eq a, Hashable a) =>          a -> OHashSet a -> OHashSet a
(>|), (|>) :: (Eq a, Hashable a) => OHashSet a ->          a -> OHashSet a

-- | /O(m*log(n)+n)/, where /m/ is the size of the smaller set and /n/ is the
-- size of the larger set.
(<>|) :: (Eq a, Hashable a) => OHashSet a -> OHashSet a -> OHashSet a

-- | /O(m*log(n)+n)/, where /m/ is the size of the smaller set and /n/ is the
-- size of the larger set.
(|<>) :: (Eq a, Hashable a) => OHashSet a -> OHashSet a -> OHashSet a

v <| o@(OHashSet ts vs)
	| v `member` o = o
	| otherwise    = OHashSet (HM.insert v t ts) (M.insert t v vs) where
		t = nextLowerTag vs

v |< o = OHashSet (HM.insert v t ts) (M.insert t v vs) where
	t = nextLowerTag vs
	OHashSet ts vs = delete v o

o@(OHashSet ts vs) |> v
	| v `member` o = o
	| otherwise    = OHashSet (HM.insert v t ts) (M.insert t v vs) where
		t = nextHigherTag vs

o >| v = OHashSet (HM.insert v t ts) (M.insert t v vs) where
	t = nextHigherTag vs
	OHashSet ts vs = delete v o

o <>| o' = unsafeMappend (o \\ o') o'
o |<> o' = unsafeMappend o (o' \\ o)

-- assumes that ts and ts' have disjoint keys
unsafeMappend (OHashSet ts vs) (OHashSet ts' vs')
	= OHashSet (HM.union tsBumped tsBumped')
	           ( M.union vsBumped vsBumped')
	where
	bump  = case maxTag vs  of
		Nothing -> 0
		Just k  -> -k-1
	bump' = case minTag vs' of
		Nothing -> 0
		Just k  -> -k
	tsBumped  = fmap (bump +) ts
	tsBumped' = fmap (bump'+) ts'
	vsBumped  = (bump +) `M.mapKeysMonotonic` vs
	vsBumped' = (bump'+) `M.mapKeysMonotonic` vs'

-- | Set difference: @r \\\\ s@ deletes all the values in @s@ from @r@. The
-- order of @r@ is unchanged.
--
-- /O(m*log(n))/ where /m/ is the size of the smaller set and /n/ is the size
-- of the larger set.
(\\) :: (Eq a, Hashable a) => OHashSet a -> OHashSet a -> OHashSet a
o@(OHashSet ts vs) \\ o'@(OHashSet ts' vs') = if size o < size o'
	then filter (not . (`member` o')) o
	else foldr delete o vs'

-- | Intersection. (@/\\@ is meant to look a bit like the standard mathematical
-- notation for intersection.)
--
-- /O(m*log(n\/(m+1)) + r*log(r))/, where /m/ is the size of the smaller set,
-- /n/ the size of the larger set, and /r/ the size of the result.
(|/\) :: (Eq a, Hashable a) => OHashSet a -> OHashSet a -> OHashSet a
OHashSet ts vs |/\ OHashSet ts' vs' = OHashSet ts'' vs'' where
	ts'' = HM.intersection ts ts'
	vs'' = M.fromList [(t, v) | (v, t) <- HM.toList ts]

-- | @flip ('|/\')@
--
-- See asymptotics of '|/\'.
(/\|) :: (Eq a, Hashable a) => OHashSet a -> OHashSet a -> OHashSet a
(/\|) = flip (/\|)

empty :: OHashSet a
empty = OHashSet HM.empty M.empty

member :: (Eq a, Hashable a) => a -> OHashSet a -> Bool
member v (OHashSet ts _) = HM.member v ts

size :: OHashSet a -> Int
size (OHashSet ts _) = HM.size ts

filter :: (a -> Bool) -> OHashSet a -> OHashSet a
filter f (OHashSet ts vs) = OHashSet (HM.filterWithKey (\v t -> f v) ts)
                                     ( M.filterWithKey (\t v -> f v) vs)

delete :: (Eq a, Hashable a) => a -> OHashSet a -> OHashSet a
delete v o@(OHashSet ts vs) = case HM.lookup v ts of
	Nothing -> o
	Just t  -> OHashSet (HM.delete v ts) (M.delete t vs)

singleton :: Hashable a => a -> OHashSet a
singleton v = OHashSet (HM.singleton v 0) (M.singleton 0 v)

-- | If a value occurs multiple times, only the first occurrence is used.
fromList :: (Eq a, Hashable a) => [a] -> OHashSet a
fromList = foldl' (|>) empty

null :: OHashSet a -> Bool
null (OHashSet ts _) = HM.null ts

findIndex :: (Eq a, Hashable a) => a -> OHashSet a -> Maybe Index
findIndex v o@(OHashSet ts vs) = do
	t <- HM.lookup v ts
	M.lookupIndex t vs

elemAt :: OHashSet a -> Index -> Maybe a
elemAt o@(OHashSet ts vs) i = do
	guard (0 <= i && i < M.size vs)
	return . snd $ M.elemAt i vs

#if MIN_VERSION_unordered_containers(0,2,10)
-- | Convert an 'OHashSet' to a 'HashSet'.
--
-- /O(n)/, where /n/ is the size of the 'OHashSet'.
toHashSet :: OHashSet a -> HashSet a
toHashSet (OHashSet ts _) = HM.keysSet ts
#endif
