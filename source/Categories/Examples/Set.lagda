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
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.Univalence

module Categories.Examples.Set where

\end{code}

We show that for subtypes, equality on subtypes is equivalent
to equality on the base type.

\begin{code}

subtype-equiv : {X : 𝓤 ̇ }
                (P : X → 𝓥 ̇ )
              → (Π x ꞉ X , is-prop (P x))
              → (x y : Σ P)
              → (x ＝ y) ≃ (pr₁ x ＝ pr₁ y)
subtype-equiv {_} {_} {X} P p (x , px) (y , py) = forwards , ((backwards , p-has-section) , (backwards , p-is-section))
 where
  h : {x : X} {px px' : P x} → px ＝ px' → x , px ＝ x , px'
  h refl = refl

  forwards : (x , px) ＝ (y , py) → x ＝ y
  forwards refl = refl

  backwards : x ＝ y → (x , px) ＝ (y , py)
  backwards refl = h (p x px py)

  p-has-section : forwards ∘ backwards ∼ id
  p-has-section refl = t (p x px py)
   where
    t : px ＝ py → (forwards ∘ backwards) refl ＝ id refl
    t refl = ap (forwards ∘ h) (props-are-sets (p x) (p x px px) refl)

  p-is-section : backwards ∘ forwards ∼ id
  p-is-section refl = ap h (props-are-sets (p x) (p x px px) refl)

\end{code}

Added by Anna Williams 24 November 2025

\begin{code}

pi-equiv-to-sum-equiv : {X : 𝓤 ̇ }
                        {P Q : X → 𝓥 ̇ }
                      → ((x : X) → (P x) ≃ (Q x))
                      → (Σ x ꞉ X , P x) ≃ (Σ x ꞉ X , Q x)
pi-equiv-to-sum-equiv {_} {_} {X} {P} {Q} pa = (λ (x , Px) → x , pr₁ (pa x) Px) , (inv , left) , (inv' , right)
 where
  inv : (Σ x ꞉ X , Q x) → (Σ x ꞉ X , P x)
  inv (x , Qx) = x , e-inverse _ (pr₂ (pa x)) Qx

  inv' : (Σ x ꞉ X , Q x) → (Σ x ꞉ X , P x)
  inv' (x , Qx) = x , pr₁ (pr₂ (pr₂ (pa x))) Qx

  left : (λ x → inv x .pr₁ , pr₁ (pa (inv x .pr₁)) (inv x .pr₂)) ∼ (λ x → x)
  left (x , Qx) = to-Σ-＝ (refl , (pr₂ (pr₁ (pr₂ (pa x))) Qx))

  right : (λ x → inv' (x .pr₁ , pr₁ (pa (x .pr₁)) (x .pr₂))) ∼ (λ x → x) 
  right (x , Px) = to-Σ-＝ (refl , pr₂ (pr₂ (pr₂ (pa x))) Px)

\end{code}

We first define the WildCategory of Sets

\begin{code}

module _ {𝓤 : Universe} where
 is-set-explicit : 𝓤 ̇ → 𝓤 ̇
 is-set-explicit A = Π a ꞉ A , Π b ꞉ A , is-prop (a ＝ b)

 Sets : 𝓤 ⁺ ̇
 Sets = Σ X ꞉ 𝓤 ̇ , is-set-explicit X

 SetWildcat : WildCategory (𝓤 ⁺) 𝓤
 SetWildcat = wildcategory
                       Sets
                       (λ (X , _) (Y , _) → (X → Y))
                       (λ x → x)
                       (λ g f x → g (f x))
                       (λ _ → refl)
                       (λ _ → refl)
                       (λ _ _ _ → refl)

 open WildCategoryNotation SetWildcat

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
     → (A ＝ B) ≃ (A ≅ B)
 lem ua fe (X , sX) (Y , sY) = ((X , sX) ＝ (Y , sY)) ≃⟨ i ⟩
                               (X ＝ Y)               ≃⟨ idtoeq X Y , ua X Y ⟩
                               (X ≃ Y)                ≃⟨ ii ⟩
                               (X , sX) ≅ (Y , sY)    ■
  where
   i : (X , sX ＝ Y , sY) ≃ (X ＝ Y)
   i = subtype-equiv is-set-explicit (λ _ → Π₂-is-prop fe
                                      (λ x y → being-prop-is-prop fe))
                                       (X , sX) (Y , sY)

   ii : (X ≃ Y) ≃ (X , sX) ≅ (Y , sY)
   ii = pi-equiv-to-sum-equiv equiv-equiv-iso
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

     lem' : (f : X → Y) → is-equiv f ≃ qinv f
     lem' f = (equivs-are-qinvs f)
            , (((qinvs-are-equivs f) , left)
            , (qinvs-are-equivs f , right))
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
         equality = g                    ＝⟨ refl ⟩
                    (λ x → id (g x))     ＝⟨ I ⟩
                    (λ x → g' (f (g x))) ＝⟨ II ⟩
                    (λ x → g' (id x))    ＝⟨ refl ⟩
                    g' ∎
          where
           I = e-inverse _ (fe _ _) (λ x → (gp' (g x))⁻¹)
           II = e-inverse _ (fe _ _) (λ x → ap g' (gp x))

     equiv-equiv-iso : (f : X → Y)
                     → is-equiv f ≃ inverse {_} {_} {_} {X , sX} {Y , sY} f
     equiv-equiv-iso f = ≃-comp (lem' f) (qinv-equiv-iso f)

 SetCat : (ua : is-univalent 𝓤)
          (fe : Fun-Ext)
        → Category (𝓤 ⁺) 𝓤
 SetCat ua fe = SetPrecat fe , univalence-property
  where
   h : (a b : obj SetWildcat) → id-to-iso a b ∼ ⌜ lem ua fe a b ⌝
   h (a , sA) b refl
    = to-Σ-＝ (refl
            , (to-Σ-＝ (refl
                     , to-×-＝ (Π-is-set fe (λ x → sA _ _) _ _)
                               (Π-is-set fe (λ x → sA _ _) _ _))))

   univalence-property : is-category (SetPrecat fe)
   univalence-property a b
    = equiv-closed-under-∼ ⌜ lem ua fe a b ⌝
                           (id-to-iso a b)
                           (pr₂ (lem ua fe a b))
                           (h a b)

\end{code}

