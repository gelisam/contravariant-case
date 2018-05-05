{-# LANGUAGE GADTs #-}
-- | 'Contravariant' functors are indexed by an @a@, but you don't have a
-- concrete value of type @a@ you can examine and pattern-match on in order to
-- guide the computation. The 'Divisible' and 'Decidable' type classes enable
-- the functionality required to pattern-match on the @a@, but they expose this
-- via an API which is hard to use. This module uses optics to re-expose this
-- functionality in a way which looks more like pattern-matching and is thus
-- hopefully more intuitive.
module ContravariantCase where

import Control.Lens
import Control.Arrow
import Data.Foldable
import Data.Functor.Contravariant.Divisible
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

-- $setup
-- >>> :set -XRankNTypes
-- >>> import Control.Lens (Fold, Getter, Lens', Prism', _Just, _Left, _Right, folded, matching, to, toListOf, worded)
-- >>> import Data.Functor.Contravariant (Predicate(..))


-- Associates a "pattern", represented by an optic and binding a single
-- variable, with the action to perform on that bound variable.
data Case newtype_ f s where
  Case :: Getting (newtype_ a) s a  -- a 'Lens'', a 'Prism'' or a 'Fold', depending on 'newtype_'
       -> f a
       -> Case newtype_ f s


-- | A version of 'view' which works with a @Getting (Identity a)@ instead of a @Getting a@.
--
-- Still works with any 'Lens'':
--
-- >>> view            _1 ("foo", "bar")
-- "foo"
-- >>> viewViaIdentity _1 ("foo", "bar")
-- "foo"
--
-- And any 'Getter':
--
-- >>> view            (to length) "foo"
-- 3
-- >>> viewViaIdentity (to length) "foo"
-- 3
viewViaIdentity :: Getting (Identity a) s a -> s -> a
viewViaIdentity getting_ = runIdentity . getConst . getting_ (Const . Identity)

-- | A version of 'Case' whose first field is a @Lens'@.
--
-- To be totally precise, we specialize the @Getting (newtype_ a) s a@ to
-- @Getting (Identity a) s a@, which is what 'viewViaIdentity' requires. Using a
-- @Lens'@ is more common though, and still typechecks because it will
-- automatically be specialized to a @Getting@:
--
-- >>> :{
-- let lensCase :: Lens' s a -> f a -> ProductCase f s
--     lensCase lens_ fx = Case lens_ fx
-- :}
--
-- @Getter@s work too:
--
-- >>> :{
-- let getterCase :: Getter s a -> f a -> ProductCase f s
--     getterCase getter fx = Case getter fx
-- :}
type ProductCase = Case Identity

-- | Match on the @a@ when @a@ is a product, dividing the work among multiple
-- fields. For 'Predicate', this means that all the fields must satisfy their
-- predicate; other 'Divisible' functors will have other semantics for 'divide'.
--
-- Each case has the form @Case (Lens' s a) (f a)@:
--
-- >>> :{
-- let onlyFooBar :: Predicate (String, String)
--     onlyFooBar = matchProduct
--       [ Case _1 $ Predicate (== "foo")
--       , Case _2 $ Predicate (== "bar")
--       ]
-- :}
--
-- >>> getPredicate onlyFooBar ("foo", "bar")
-- True
-- >>> getPredicate onlyFooBar ("foo", "baz")
-- False
--
-- 'Getter's work too:
--
-- >>> :{
-- let onlyThreeLetterWordsBeginningWithF :: Predicate String
--     onlyThreeLetterWordsBeginningWithF = matchProduct
--       [ Case (to length)   $ Predicate (== 3)
--       , Case (to (take 1)) $ Predicate (== "f")
--       ]
-- :}
--
-- >>> getPredicate onlyThreeLetterWordsBeginningWithF "foo"
-- True
-- >>> getPredicate onlyThreeLetterWordsBeginningWithF "bar"
-- False
matchProduct :: Divisible f => [ProductCase f s] -> f s
matchProduct []                       = conquer
matchProduct (Case getter fx : cases) = divide (viewViaIdentity getter &&& id)
                                               fx
                                               (matchProduct cases)


-- | A version of 'matching' which works with a @Getting (First a)@ instead of a @Prism'@.
--
-- Still works with any 'Prism'':
--
-- >>> matching         _Just <$> [Just "foo", Nothing]
-- [Right "foo",Left Nothing]
-- >>> matchingViaFirst _Just <$> [Just "foo", Nothing]
-- [Right "foo",Left Nothing]
matchingViaFirst :: Getting (First a) s a -> s -> Either s a
matchingViaFirst getting_ s = maybe (Left s) Right
                            . preview getting_
                            $ s

-- | A version of 'Case' whose first field is a @Prism'@.
--
-- To be totally precise, we specialize the @Getting (newtype_ a) s a@ to
-- @Getting (First a) s a@, which is what 'matchingViaFirst' requires. Using a
-- @Prism'@ is more common though, and still typechecks because it will
-- automatically be specialized to a @Getting@:
--
-- >>> :{
-- let prismCase :: Prism' s a -> f a -> SumCase f s
--     prismCase prism_ fx = Case prism_ fx
-- :}
type SumCase = Case First

-- | Match on the @a@ when @a@ is a sum, choosing which work to do depending on
-- @a@'s constructor. Only the first matching 'Case' will be used. All of @a@'s
-- constructors must be covered, just like with ordinary pattern-matching, but
-- be careful! Unlike with regular pattern-matching, if you add a new
-- constructor to @a@, the compiler will not warn you if you forget to add a
-- case corresponding to this new constructor.
--
-- Each case has the form @Case (Prism' s a) (f a)@:
--
-- >>> :{
-- let onlyLeftFooOrRightBar :: Predicate (Either String String)
--     onlyLeftFooOrRightBar = matchSum
--       [ Case _Left  $ Predicate (== "foo")
--       , Case _Right $ Predicate (== "bar")
--       ]
-- :}
--
-- >>> getPredicate onlyLeftFooOrRightBar (Left "foo")
-- True
-- >>> getPredicate onlyLeftFooOrRightBar (Right "bar")
-- True
-- >>> getPredicate onlyLeftFooOrRightBar (Right "foo")
-- False
matchSum :: Decidable f => [SumCase f s] -> f s
matchSum []                       = lose $ \_ -> error "matchSum: no match"
matchSum (Case prism_ fx : cases) = choose (matchingViaFirst prism_)
                                           (matchSum cases)
                                           fx


-- | Divide the work among all the elements of the list. For 'Predicate', this
-- means that all the elements must satisfy the given predicate; other
-- 'Divisible' functors will have other semantics for 'divide'.
--
-- >>> :{
-- let allEven :: Predicate [Int]
--     allEven = contraFold (Predicate even)
-- :}
--
-- >>> getPredicate allEven [2,4,6]
-- True
-- >>> getPredicate allEven [2,4,7]
-- False
contraFold :: Decidable f => f a -> f [a]
contraFold fx = matchSum
  [ Case _Empty $ conquer
  , Case _Cons  $ matchProduct
    [ Case _1 $ fx
    , Case _2 $ contraFold fx
    ]
  ]


-- | A version of 'toListOf' which works with a @Getting (Seq a)@ instead of a @Getting (Endo [a]@.
--
-- Still works with any 'Fold':
--
-- >>> toListOf        worded "hello world"
-- ["hello","world"]
-- >>> toListOfViaSeq  worded "hello world"
-- ["hello","world"]
toListOfViaSeq :: Getting (Seq a) s a -> s -> [a]
toListOfViaSeq getting_ = toList
                        . foldMapOf getting_ Seq.singleton

-- | A version of 'Case' whose first field is a @Fold@.
--
-- To be totally precise, we specialize the @Getting (newtype_ a) s a@ to
-- @Getting (Seq a) s a@, which is what 'toListOfViaSeq' requires. Using a
-- @Fold@ is more common though, and still typechecks because it will
-- automatically be specialized to a @Getting@:
--
-- >>> :{
-- let foldCase :: Fold s a -> f a -> FoldCase f s
--     foldCase fold_ fx = Case fold_ fx
-- :}
type FoldCase = Case Seq

-- | Divide the work among multiple subsets of @a@, using 'Fold's to select
-- those subsets. For 'Predicate', this means that all the pieces selected by
-- all the 'Fold's must satisfy their predicate; other 'Divisible' functors will
-- have other semantics for 'divide'.
--
-- This can be used as shorthand for nested 'matchSum' and 'matchProduct' calls.
-- For example, here is an alternate implementation of 'contraFold':
--
-- >>> :{
-- let contraFold' :: Decidable f => f a -> f [a]
--     contraFold' fx = matchFold
--       [ Case _Empty $ conquer
--       , Case (_Cons . _1) $ fx
--       , Case (_Cons . _2) $ contraFold' fx
--       ]
-- :}
--
-- >>> getPredicate (contraFold' . Predicate $ even) $ [2,4,6::Int]
-- True
-- >>> getPredicate (contraFold' . Predicate $ even) $ [2,4,7::Int]
-- False
--
-- Unlike 'matchProduct', a single case can select more than one piece:
--
-- >>> :{
-- let allEven' :: Predicate [Int]
--     allEven' = matchFold [Case folded $ Predicate even]
-- :}
--
-- >>> getPredicate allEven' $ [2,4,6]
-- True
-- >>> getPredicate allEven' $ [2,4,7]
-- False
--
-- And unlike 'matchSum', not all the constructors need to be covered:
--
-- >>> :{
-- let fooOrNothing :: Predicate (Maybe String)
--     fooOrNothing = matchFold [Case _Just $ Predicate (== "foo")]
-- :}
--
-- >>> getPredicate fooOrNothing (Just "foo")
-- True
-- >>> getPredicate fooOrNothing (Just "bar")
-- False
-- >>> getPredicate fooOrNothing Nothing
-- True
matchFold :: Decidable f => [FoldCase f s] -> f s
matchFold []                      = conquer
matchFold (Case fold_ fx : cases) = divide (toListOfViaSeq fold_ &&& id)
                                           (contraFold fx)
                                           (matchFold cases)
