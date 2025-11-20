Anna Williams, 12 November 2025

The Category of Sets

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Type renaming (id to c-id)
open import MLTT.Spartan hiding (_∘_)
open import UF.Base
open import UF.Equiv hiding (_≅⟨_⟩_)
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

module Categories.Examples.Set where

\end{code}

We first define the WildCategory of Sets

\begin{code}

module _ {𝓤 : Universe} where
 is-set-explicit : 𝓤 ̇ → 𝓤 ̇
 is-set-explicit A = Π a ꞉ A , Π b ꞉ A , is-prop (a ＝ b)

 Sets : 𝓤 ⁺ ̇
 Sets = Σ X ꞉ 𝓤 ̇ , is-set-explicit X

 SetWildcat : WildCategory (𝓤 ⁺) 𝓤
 SetWildcat = wildcat-make
                       Sets
                       (λ (X , _) (Y , _) → (X → Y))
                       (λ x → x)
                       (λ g f x → g (f x))
                       (λ _ → refl)
                       (λ _ → refl)
                       refl

\end{code}

We can now define the precategory of sets.

\begin{code}

 SetPrecat : (fe : Fun-Ext) → Precategory (𝓤 ⁺) 𝓤
 SetPrecat fe = (SetWildcat , set-is-precat)
  where
   set-is-precat : is-precategory SetWildcat
   set-is-precat (X , sX) (Y , sY) {x} {y} = Π-is-set fe (λ - {a} {b} → sY a b) {x} {y}

\end{code}

And finally the category of sets.

\begin{code}

 lem : (ua : is-univalent 𝓤)
       (fe : Fun-Ext)
       (A B : Sets)
     → (A ＝ B) ≃ (A ≅⟨ SetWildcat ⟩ B)
 lem ua fe (X , sX) (Y , sY) = ((X , sX) ＝ (Y , sY))            ≃⟨ i ⟩
                               (X ＝ Y)                          ≃⟨ idtoeq X Y , ua X Y ⟩
                               (X ≃ Y)                           ≃⟨ ii ⟩
                               (X , sX) ≅⟨ SetWildcat ⟩ (Y , sY) ■
  where
   i : (X , sX ＝ Y , sY) ≃ (X ＝ Y)
   i = subtype-equiv is-set-explicit (λ _ → Π-is-prop fe
                                      (λ x → Π-is-prop fe (λ y → being-prop-is-prop fe)))
                                     (X , sX) (Y , sY)

   ii : (X ≃ Y) ≃ wildcat-iso-explicit SetWildcat (X , sX) (Y , sY)
   ii = {!!}

 SetCat : (ua : is-univalent 𝓤)
          (fe : Fun-Ext)
        → Category (𝓤 ⁺) 𝓤
 SetCat ua fe = SetPrecat fe , univalence-property
  where
   univalence-property : is-category (SetPrecat fe)
   univalence-property (X , sX) (Y , sY) = {!!}

\end{code}

