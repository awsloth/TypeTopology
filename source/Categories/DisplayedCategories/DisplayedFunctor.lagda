Anna Williams, 30 October 2025

Definition of a displayed functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.DependentEquality

module Categories.DisplayedCategories.DisplayedFunctor where

open import Categories.Type
open import Categories.Functor
open import Categories.DisplayedCategories.Type

record DisplayedFunctor {C : Precategory 𝓦 𝓣}
                        {C' : Precategory 𝓦' 𝓣'}
                        (F' : Functor ⟨ C ⟩ ⟨ C' ⟩)
                        (D : DisplayedPrecategory 𝓤 𝓥 C)
                        (D' : DisplayedPrecategory 𝓤' 𝓥' C')
                      : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') ̇  where
 open CategoryNotation ⟨ C ⟩
 open FunctorNotation F' renaming (functor-map to F)
 open DisplayedNotation D
 open DisplayedNotation D'
 field
  obj-map : {c : obj C}
          → obj[ c ]
          → obj[ F c ]
  hom-map : {c c' : obj C}
            {f : hom c c'}
            {x : obj[ c ]}
            {y : obj[ c' ]}
          → hom[ f ] x y
          → hom[ F f ] (obj-map x) (obj-map y)
  id-map-pres : {c : obj C}
                {a : obj[ c ]}
              → hom-map disp-id
              ＝⟦ (λ - → hom[ - ] (obj-map a) (obj-map a)) , id-pres c ⟧
                disp-id
  map-distrib : {a b c : obj ⟨ C ⟩}
                {x : obj[ a ]}
                {y : obj[ b ]}
                {z : obj[ c ]}
                {f' : hom a b}
                {g' : hom b c}
                {f : hom[ f' ] x y}
                {g : hom[ g' ] y z}
              → hom-map (g ∘' f) ＝⟦ (λ - → hom[ - ] _ _) , distrib g' f' ⟧ hom-map g ∘' hom-map f

\end{code}
