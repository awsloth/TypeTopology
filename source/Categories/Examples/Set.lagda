Anna Williams, 12 November 2025

The Category of Sets

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Wild
open import Categories.Pre
open import Categories.Univalent
open import Categories.Notation.Wild hiding (⌜_⌝)
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_≅_) renaming (inverse to e-inverse)
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.Univalence

module Categories.Examples.Set where

\end{code}

First we define Sets under a given universe 𝓤. We first define sets, which is a
type A, such that for all a b : A, a ＝ b is a proposition.

\begin{code}

module _ {𝓤 : Universe} where
 is-set-explicit : 𝓤 ̇ → 𝓤 ̇
 is-set-explicit A = Π a ꞉ A , Π b ꞉ A , is-prop (a ＝ b)

 Sets : 𝓤 ⁺ ̇
 Sets = Σ X ꞉ 𝓤 ̇ , is-set-explicit X

\end{code}

We can now easily define the wild category of sets.

\begin{code}

 SetWildCategory : WildCategory (𝓤 ⁺) 𝓤
 SetWildCategory = wildcategory Sets
                                (λ (X , _) (Y , _) → (X → Y))
                                id
                                _∘_
                                (λ _ → refl)
                                (λ _ → refl)
                                (λ _ _ _ → refl)

 open WildCategoryNotation SetWildCategory

\end{code}

We can now define the precategory of sets.

\begin{code}

 SetPrecategory : (fe : Fun-Ext) → Precategory (𝓤 ⁺) 𝓤
 SetPrecategory fe = (SetWildCategory , set-is-precategory)
  where
   set-is-precategory : is-precategory SetWildCategory
   set-is-precategory (X , sX) (Y , sY) {x} {y}
    = Π-is-set fe (λ _ → sY _ _) {x} {y}

\end{code}

And finally the category of sets. Notice that this proof can also
be done using SIP.

\begin{code}

 id-equiv-iso : (ua : is-univalent 𝓤)
       (fe : Fun-Ext)
       (A B : Sets)
     → (A ＝ B) ≃ (A ≅ B)
 id-equiv-iso ua fe (X , sX) (Y , sY) = ((X , sX) ＝ (Y , sY)) ≃⟨ i ⟩
                                        (X ＝ Y)               ≃⟨ ii ⟩
                                        (X ≃ Y)                ≃⟨ iii ⟩
                                        (X , sX) ≅ (Y , sY)    ■
  where
   i : (X , sX ＝ Y , sY) ≃ (X ＝ Y)
   i = subtype-equiv is-set-explicit (λ _ → Π₂-is-prop fe
                                      (λ x y → being-prop-is-prop fe))
                                       (X , sX) (Y , sY)

   ii : (X ＝ Y) ≃ (X ≃ Y)
   ii = idtoeq X Y , ua X Y

   iii : (X ≃ Y) ≃ (X , sX) ≅ (Y , sY)
   iii = Σ-cong equiv-equiv-iso
    where
     qinv-equiv-iso : (f : X → Y)
                    → qinv f ≃ inverse {_} {_} {_} {X , sX} {Y , sY} f
     qinv-equiv-iso f = forwards , ((backwards , left) , (backwards , right))
      where
       forwards : qinv f → inverse {_} {_} {_} {X , sX} {Y , sY} f
       forwards (g , lg , rg) = g , (dfunext fe lg , dfunext fe rg)

       backwards : inverse {_} {_} {_} {X , sX} {Y , sY} f → qinv f
       backwards (g , lg , rg) = g
                               , (λ x → ap (λ - → - x) lg)
                               , λ y → ap (λ - → - y) rg

       left : (λ x → forwards (backwards x)) ∼ id
       left (g , lg , rg) = to-Σ-＝ (refl
                                  , (to-×-＝ (Π-is-set fe (λ x → sX _ _) _ _)
                                             (Π-is-set fe (λ y → sY _ _) _ _)))

       right : (λ x → backwards (forwards x)) ∼ id
       right (g , lg , rg) = to-Σ-＝ (refl
                                   , (to-×-＝ (dfunext fe (λ x → sX _ _ _ _))
                                              (dfunext fe (λ y → sY _ _ _ _))))

     is-equiv-equiv-qinv : (f : X → Y) → is-equiv f ≃ qinv f
     is-equiv-equiv-qinv f = (equivs-are-qinvs f)
                           , (qinvs-are-equivs f , left)
                           , (qinvs-are-equivs f , right)
      where
       left : (λ x → equivs-are-qinvs f (qinvs-are-equivs f x)) ∼ (λ x → x)
       left e@(g , gl , gr) = to-Σ-＝ (refl
                                    , (to-×-＝ (dfunext fe (λ x → sX _ _ _ _))
                                               refl))

       right : (λ x → qinvs-are-equivs f (equivs-are-qinvs f x)) ∼ (λ x → x)
       right e@((g , gp) , (g' , gp'))
        = to-×-＝ refl (to-Σ-＝ (equality , (dfunext fe λ x → sX _ _ _ _)))
        where
         equality : g ＝ g'
         equality = g          ＝⟨ refl ⟩
                    id ∘ g     ＝⟨ I ⟩
                    g' ∘ f ∘ g ＝⟨ II ⟩
                    g' ∘ id    ＝⟨ refl ⟩
                    g'         ∎
          where
           I = e-inverse _ (fe _ _) (λ x → (gp' (g x))⁻¹)
           II = e-inverse _ (fe _ _) (λ x → ap g' (gp x))

     equiv-equiv-iso : (f : X → Y)
                     → is-equiv f ≃ inverse {_} {_} {_} {X , sX} {Y , sY} f
     equiv-equiv-iso f = ≃-comp (is-equiv-equiv-qinv f) (qinv-equiv-iso f)

\end{code}

We can finally prove that Set forms a category.

\begin{code}

 SetCategory : (ua : is-univalent 𝓤)
               (fe : Fun-Ext)
             → Category (𝓤 ⁺) 𝓤
 SetCategory ua fe = SetPrecategory fe , univalence-property
  where
   h : (a b : obj SetWildCategory) → id-to-iso a b ∼ ⌜ id-equiv-iso ua fe a b ⌝
   h (a , sA) b refl
    = to-Σ-＝ (refl
            , (to-Σ-＝ (refl
                     , to-×-＝ (Π-is-set fe (λ x → sA _ _) _ _)
                               (Π-is-set fe (λ x → sA _ _) _ _))))

   univalence-property : is-category (SetPrecategory fe)
   univalence-property a b
    = equiv-closed-under-∼ ⌜ id-equiv-iso ua fe a b ⌝
                           (id-to-iso a b)
                           (pr₂ (id-equiv-iso ua fe a b))
                           (h a b)

\end{code}

