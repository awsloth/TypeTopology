Anna Williams 25 February 2026

Category of Magmas via displayed categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Examples.Set
open import Categories.Examples.Magma
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Total

module Categories.Displayed.Examples.Magma where

\end{code}

We define the category (wow)

\begin{code}


module _ {𝓤 : Universe} {fe : Fun-Ext} where

 instance
  underlying-set : Underlying-Type Sets (𝓤 ̇  )
  ⟨_⟩ ⦃ underlying-set ⦄ (S , _) = S

 DMagma : DisplayedPrecategory 𝓤 𝓤 (SetPrecat fe)
 DMagma = record
          { obj[_] = λ (A , _) → (A → A → A)
          ; hom[_] = λ {(A , _)} f _·_ _*_ → (x y : A) → f (x · y) ＝ f x * f y
          ; hom[-]-is-set = λ {_} {(_ , sB)} → Π₂-is-set fe λ x y → props-are-sets (sB _ _)
          ; D-𝒊𝒅 = λ _ _ → refl
          ; _○_ = λ {_} {_} {_} {g} {f} {_·_} {_*_} {_∙_} gmagma fmagma x y
                → g (f (x · y))     ＝⟨ ap g (fmagma x y) ⟩
                  g (f x * f y)     ＝⟨ gmagma (f x) (f y) ⟩
                  g (f x) ∙ g (f y) ∎
          ; D-𝒊𝒅-is-right-neutral = λ {_} {_} {f} {_·_} {_*_} 𝕗 → dfunext fe λ x → dfunext fe λ y → {!!}
          ; D-𝒊𝒅-is-left-neutral = λ {_} {_} {f} {_·_} {_*_} 𝕗 → dfunext fe λ x → dfunext fe λ y → {!!}
          ; D-assoc = {!!}
          }

 MagmaTot : Precategory (𝓤 ⁺) 𝓤
 MagmaTot = TotalPrecategory DMagma

 DMagmaCat : DisplayedCategory 𝓤 𝓤 (SetPrecat fe)
 DMagmaCat = DMagma , λ {a} {b} e x y → equivalence a b e x y
  where
   open DispPrecatNotation DMagma
   equivalence : (a : obj (SetPrecat fe))
                 (b : obj (SetPrecat fe))
                 (e : a ＝ b)
                 (x : obj[ a ])
                 (y : obj[ b ])
               → is-equiv (D-id-to-iso DMagma {a} {b} e x y)
   equivalence a b refl _·_ _*_ = {!!} , {!!}
 
\end{code}
