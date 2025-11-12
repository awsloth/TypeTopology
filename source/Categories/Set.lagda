Anna Williams, 12 November 2025

The Category of Sets

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Type
open import MLTT.Spartan
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties

module Categories.Set where

\end{code}

We first define the WildCategory of Sets

\begin{code}

SetWildcat : {𝓤 : Universe} → WildCategory (𝓤 ⁺) 𝓤
SetWildcat {𝓤} = wildcat-make (Σ S ꞉ 𝓤 ̇ , is-set S)
                      (λ (X , _) (Y , _) → X → Y)
                      (λ x → x)
                      (λ g f x → g (f x))
                      (λ _ → refl)
                      (λ _ → refl)
                      refl

\end{code}

We can now define the precategory of sets.

\begin{code}

SetPrecat : {𝓤 : Universe} (fe : Fun-Ext)
          → Precategory (𝓤 ⁺) 𝓤
SetPrecat fe = (SetWildcat , set-is-precat)
 where
  set-is-precat : is-precategory SetWildcat
  set-is-precat (X , sX) (Y , sY) = Π-is-set fe λ _ → sY

\end{code}

And finally the category of sets.

\begin{code}

SetCat : {𝓤 : Universe}
         (fe : Fun-Ext)
       → Category (𝓤 ⁺) 𝓤
SetCat fe = SetPrecat fe , univalence-property
 where
  univalence-property : is-category (SetPrecat fe)
  univalence-property = {!!}

\end{code}
