# Contravariant `case`

[`Contravariant`](http://hackage.haskell.org/package/contravariant-1.4.1/docs/Data-Functor-Contravariant.html#t:Contravariant) functors are indexed by an `a`, but you don't have a concrete value of type `a` you can examine and pattern-match on in order to guide the computation. The [`Divisible`](http://hackage.haskell.org/package/contravariant-1.4.1/docs/Data-Functor-Contravariant-Divisible.html#t:Divisible) and [`Decidable`](http://hackage.haskell.org/package/contravariant-1.4.1/docs/Data-Functor-Contravariant-Divisible.html#t:Decidable) type classes enable the functionality required to pattern-match on the `a`, but they expose this via an API which is hard to use. This package uses optics to re-expose this functionality in a way which looks more like pattern-matching and is thus hopefully more intuitive.

## Without `contravariant-case`

For example, let's try to implement a combinator which lifts a [`Predicate`](http://hackage.haskell.org/package/contravariant-1.4.1/docs/Data-Functor-Contravariant.html#t:Predicate) on elements to a `Predicate` on lists by making sure the `Predicate` accepts every element of the list. Implementing this using the methods provided by the [`contravariant`](http://hackage.haskell.org/package/contravariant) package requires us to convert the list into its sum-of-products representation, `Either () (a, [a])`:

    listToSOP :: [a] -> Either () (a, [a])
    listToSOP []     = Left ()
    listToSOP (x:xs) = Right (x, xs)

And we need to pay close attention to this representation in order to determine the parts of the list on which the `allSatisfy` implementation applies `conquer`, `p`, and the recursive call `allSatisfy p`:

    allSatisfy :: Predicate a -> Predicate [a]
    allSatisfy p = choose listToSOP conquer (divide id p (allSatisfy p))

## With `contravariant-case`

With this package, we can write an implementation of `allSatisfy` which doesn't require `listToSOP`, and instead looks like we are pattern-matching on the list:

    allSatisfy :: Predicate a -> Predicate [a]
    allSatisfy p = matchSum
      [ Case _Empty $ conquer
      , Case _Cons  $ matchProduct
        [ Case _1 $ p
        , Case _2 $ allSatisfy p
        ]
      ]

The `_Empty` and `_Cons` patterns are [`Prism`](http://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Prism.html)s, while the `_1` and `_2` patterns are [`Getter`](https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Getter.html)s. The [`lens`](http://hackage.haskell.org/package/lens) library can [generate](http://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-TH.html) those for any algebraic datatype.

The `allSatisfy` implementation above alternates between `matchSum` and `matchProduct` in order to get to the elements. This pattern is very common, and so we provide a shortcut. The following alternate implementation mixes `Prism`s and `Getter`s within the same `matchFold`:

    allSatisfy :: Predicate a -> Predicate [a]
    allSatisfy p = matchFold
      [ Case _Empty $ conquer
      , Case (_Cons . _1) $ p
      , Case (_Cons . _2) $ allSatisfy p
      ]

`matchFold` uses the fact that combining a `Prism` with a `Getter` gives a [`Fold`](https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Fold.html)s. While the 'Fold`s obtained by combining a `Prism` with a `Fold` will always focus on at most one element, in general `Fold`s can focus on multiple elements. We can use such a `Fold` to write an even shorter implementation:

    allSatisfy :: Predicate a -> Predicate [a]
    allSatisfy p = matchFold [Case each p]
