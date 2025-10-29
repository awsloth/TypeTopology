Anna Williams, 29 October 2025

Examples involving displayed categories

\begin{code}


{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Groups.Type
open import Categories.Category
open import Categories.DisplayedCategories.DisplayedCategory

module Categories.DisplayedCategories.DisplayedExamples where

set-cat : Category 𝓤₂ 𝓤₁
set-cat = record { precategory = record
                                  { obj = 𝓤₁ ̇
                                  ; hom = λ A B → (A → B)
                                  ; hom-is-set = {!!}
                                  ; id = λ f x → x
                                  ; _∘_ = λ g f A → g (f A)
                                  ; left-id = λ f → refl
                                  ; right-id = λ f → refl
                                  ; assoc = refl
                                  } ; id-equiv-iso = {!!}}

disp-grp : DisplayedCategory {!!} {!!} (set-cat)
disp-grp = record
            { obj-fam = (λ X → Group-structure X)
            ; mor-fam = {!!}
            ; mor-fam-is-set = {!!}
            ; id-fam = {!!}
            ; comp = {!!}
            ; cmp-right-id = {!!}
            ; cmp-left-id = {!!}
            ; cmp-assoc = {!!}
            }

\end{code}
