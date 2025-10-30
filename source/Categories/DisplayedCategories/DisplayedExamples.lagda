Anna Williams, 29 October 2025

Examples involving displayed categories

\begin{code}


{-# OPTIONS --safe --without-K #-}

open import Groups.Type
open import MLTT.Spartan
open import UF.Sets

open import Categories.Category
open import Categories.DisplayedCategories.DisplayedCategory

module Categories.DisplayedCategories.DisplayedExamples where


-- Couldn't figure out how to show that is-set (𝓤₁), maybe this isn't necessarily true? 
module _ (𝓤 : Universe) (i : is-set (𝓤 ̇ )) where
 set-cat : Category (𝓤 ⁺) 𝓤
 set-cat = record { precategory = record
                                 { obj = 𝓤 ̇
                                 ; hom = λ A B → (A → B)
                                 ; hom-is-set = {!!} -- via funext
                                 ; id = λ A a → a
                                 ; _∘_ = λ g f a → g (f a)
                                 ; left-id = λ f → refl
                                 ; right-id = λ f → refl
                                 ; assoc = refl
                                 } ; id-equiv-iso = {!!}} -- via UA

 disp-grp : DisplayedCategory 𝓤 𝓤 (set-cat)
 disp-grp = record
             { obj-fam = λ X → Group-structure X
             ; mor-fam = λ {a} {b} f A B → is-hom (a , A) (b , B) f
             ; mor-fam-is-set = {!!}
             ; id-fam = λ {c} C → id-is-hom (c , C)
             ; comp = λ {a} {b} {c} {g} {f} {A} {B} {C} G F → ∘-is-hom (a , A) (b , B) (c , C) f g F G
             ; cmp-right-id = λ f → {!!}
             ; cmp-left-id = λ f → {!!}
             ; cmp-assoc = {!!}
             }

\end{code}
