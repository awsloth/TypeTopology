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
 -- This may need changing
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
                       (λ _ _ _ → refl)

\end{code}

We can now define the precategory of sets.

\begin{code}

 SetPrecat : (fe : Fun-Ext) → Precategory (𝓤 ⁺) 𝓤
 SetPrecat fe = (SetWildcat , set-is-precat)
  where
   set-is-precat : is-precategory SetWildcat
   set-is-precat (X , sX) (Y , sY) {x} {y}
    = Π-is-set fe (λ - {a} {b} → sY a b) {x} {y}

\end{code}

And finally the category of sets. Notice that this proof can also
be done using SIP.

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
   i = subtype-equiv is-set-explicit (λ _ → Π₂-is-prop fe
                                      (λ x y → being-prop-is-prop fe))
                                       (X , sX) (Y , sY)

   ii : (X ≃ Y) ≃ wildcat-iso-explicit SetWildcat (X , sX) (Y , sY)
   ii = pi-equiv-to-sum-equiv equiv-equiv-iso
    where
     qinv-equiv-iso : (f : X → Y) → qinv f ≃ is-iso {{SetWildcat}} {X , sX} {Y , sY} f
     qinv-equiv-iso f = forwards , ((backwards , left) , (backwards , right))
      where
       forwards : qinv f → is-iso {{SetWildcat}} {X , sX} {Y , sY} f
       forwards (g , lg , rg) = g , (inverse _ (fe _ _) lg , inverse _ (fe _ _) rg)

       backwards : is-iso {{SetWildcat}} {X , sX} {Y , sY} f → qinv f
       backwards (g , lg , rg) = g , (λ x → ap (λ - → - x) lg) , λ y → ap (λ - → - y) rg

       left : (λ x → forwards (backwards x)) ∼ id
       left (g , lg , rg) = to-Σ-＝ (refl , (to-×-＝ (Π-is-set fe (λ x → sX _ _) _ _) (Π-is-set fe (λ y → sY _ _) _ _)))

       right : (λ x → backwards (forwards x)) ∼ id
       right (g , lg , rg) = to-Σ-＝ (refl , (to-×-＝ (inverse _ (fe _ _) (λ x → sX _ _ _ _)) (inverse _ (fe _ _) (λ y → sY _ _ _ _))))

     lem' : (f : X → Y) → is-equiv f ≃ qinv f
     lem' f = (equivs-are-qinvs f) , (((qinvs-are-equivs f) , left) , (qinvs-are-equivs f , right))
      where
       left : (λ x → equivs-are-qinvs f (qinvs-are-equivs f x)) ∼ (λ x → x)
       left e@(g , gl , gr) = to-Σ-＝ (refl , (to-×-＝ (inverse _ (fe _ _) (λ x → sX _ _ _ _)) refl))

       right : (λ x → qinvs-are-equivs f (equivs-are-qinvs f x)) ∼ (λ x → x)
       right e@((g , gp) , (g' , gp')) = to-×-＝ refl (to-Σ-＝ (equality , (inverse _ (fe _ _) λ x → sX _ _ _ _)))
        where
         equality : g ＝ g'
         equality = g                    ＝⟨ refl ⟩
                    (λ x → id (g x))     ＝⟨ inverse _ (fe _ _) (λ x → (gp' (g x))⁻¹) ⟩
                    (λ x → g' (f (g x))) ＝⟨ inverse _ (fe _ _) (λ x → ap g' (gp x)) ⟩
                    (λ x → g' (id x))    ＝⟨ refl ⟩
                    g' ∎

     equiv-equiv-iso : (f : X → Y) → is-equiv f ≃ is-iso {{SetWildcat}} {X , sX} {Y , sY} f
     equiv-equiv-iso f = ≃-comp (lem' f) (qinv-equiv-iso f)

 SetCat : (ua : is-univalent 𝓤)
          (fe : Fun-Ext)
        → Category (𝓤 ⁺) 𝓤
 SetCat ua fe = SetPrecat fe , univalence-property
  where
   h : (a b : obj SetWildcat) → id-to-iso {{SetWildcat}} a b ∼ ⌜ lem ua fe a b ⌝
   h (a , sA) b refl = to-Σ-＝ (refl , (to-Σ-＝ (refl , to-×-＝ (Π-is-set fe (λ x → sA _ _) _ _) (Π-is-set fe (λ x → sA _ _) _ _))))

   univalence-property : is-category (SetPrecat fe)
   univalence-property a b = equiv-closed-under-∼ ⌜ lem ua fe a b ⌝ (id-to-iso {{SetWildcat}} a b) (pr₂ (lem ua fe a b)) (h a b)
\end{code}

