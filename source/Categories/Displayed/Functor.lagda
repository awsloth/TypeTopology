Anna Williams, 30 October 2025

Definition of a displayed functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.DependentEquality

module Categories.Displayed.Functor where

open import Categories.Pre
open import Categories.Functor
open import Categories.Notation.Wild
open import Categories.Notation.Pre
open import Categories.Notation.Functor
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre

\end{code}

We define displayed functors analagously to functors, but like displayed
precategories we work with some "base" functor, with which we map between the
base precategories which lie below the displayed precategories.

\begin{code}

record DisplayedFunctor {P : Precategory 𝓦 𝓣}
                        {P' : Precategory 𝓦' 𝓣'}
                        (F' : Functor ⟨ P ⟩ ⟨ P' ⟩)
                        (D : DisplayedPrecategory 𝓤 𝓥 P)
                        (D' : DisplayedPrecategory 𝓤' 𝓥' P')
                      : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') ̇  where
 open PrecategoryNotation P
 open FunctorNotation F' renaming (functor-map to F)
 open DisplayedNotation D
 open DisplayedNotation D'
 field
  obj-map : {c : obj P}
          → obj[ c ]
          → obj[ F c ]
  hom-map : {c c' : obj P}
            {f : hom c c'}
            {x : obj[ c ]}
            {y : obj[ c' ]}
          → hom[ f ] x y
          → hom[ F f ] (obj-map x) (obj-map y)
  id-map-pres : {c : obj P}
                {a : obj[ c ]}
              → hom-map disp-id
              ＝⟦ (λ - → hom[ - ] (obj-map a) (obj-map a)) , id-preserved c ⟧
                disp-id
  map-distrib : {a b c : obj P}
                {x : obj[ a ]}
                {y : obj[ b ]}
                {z : obj[ c ]}
                {f' : hom a b}
                {g' : hom b c}
                {f : hom[ f' ] x y}
                {g : hom[ g' ] y z}
              → hom-map (g ∘' f) ＝⟦ (λ - → hom[ - ] _ _) , distributivity g' f' ⟧ hom-map g ∘' hom-map f

\end{code}
