Anna Williams 25 February 2026

Category of Magmas via displayed categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv
open import UF.FunExt
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
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

We define the precategory of magmas.

\begin{code}


module _ {𝓤 : Universe} {fe : Fun-Ext} where
 open PrecategoryNotation (SetPrecat {𝓤} fe)

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
          ; D-𝒊𝒅-is-right-neutral = λ {_} {(_ , sB)} 𝕗 → (dfunext fe λ _ → dfunext fe λ _ → sB _ _ _ _)
          ; D-𝒊𝒅-is-left-neutral = λ {_} {(_ , sB)} 𝕗 → (dfunext fe λ _ → dfunext fe λ _ → sB _ _ _ _)
          ; D-assoc = λ {_} {_} {_} {(_ , sD)} → (dfunext fe λ x → dfunext fe λ y → sD _ _ _ _)
          }

 MagmaTot : Precategory (𝓤 ⁺) 𝓤
 MagmaTot = TotalPrecategory DMagma

\end{code}

We now defined the category of magmas.

\being{code}

 open DispPrecatNotation DMagma

 DMagmaCat : DisplayedCategory 𝓤 𝓤 (SetPrecat fe)
 DMagmaCat = DMagma , λ {a} {b} e x y → equivalence a b e x y
  where
   equivalence : (a : obj (SetPrecat fe))
                 (b : obj (SetPrecat fe))
                 (e : a ＝ b)
                 (x : obj[ a ])
                 (y : obj[ b ])
               → is-equiv (D-id-to-iso DMagma {a} {b} e x y)
   equivalence a@(A , sA) b refl _·_ _*_ = (forwards , f-is-thing) , (forwards , f-has-thing) 
    where
     forwards : _≅[_]_ {_} {_} {_} {_} {_} {_} {a} {a} _·_ (id , id , refl , refl) _*_
              → dependent-Id obj[_] {a} refl _·_ _*_
     forwards (f , g , for , bac) = dfunext fe λ x → dfunext fe λ y → f x y

     f-is-thing : (λ x → D-id-to-iso DMagma refl _·_ _*_ (forwards x)) ∼ (λ x → x)
     f-is-thing (f , g , for , bac) = to-Σ-＝ (Π₂-is-prop fe (λ x y → sA _ _) _ _
                                            , to-Σ-＝ ((Π₂-is-prop fe (λ x y → sA _ _) _ _)
                                            , to-×-＝ (Π₂-is-set fe (λ x y → props-are-sets (sA _ _)) _ _)
                                                      (Π₂-is-set fe (λ x y → props-are-sets (sA _ _)) _ _)))

     f-has-thing : (λ x → forwards (D-id-to-iso DMagma refl _·_ _*_ x)) ∼ (λ x → x)
     f-has-thing x = Π₂-is-set fe (λ x y → sA _ _) _ _

\end{code}
