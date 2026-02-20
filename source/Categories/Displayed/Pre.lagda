Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.DependentEquality
open import UF.Equiv hiding (_≅_ ; inverse ; ⌜_⌝)
open import UF.Sets
open import Categories.Pre
open import Categories.Notation.Pre

module Categories.Displayed.Pre where


\end{code}

We first define the notion of a displayed precategory. The objects and homs of
this are indexed by a given base precategory. We then derive the other parts of
a precategory, including the usual axioms which now have dependent equalities.

More precisely, a displayed precategory over a precategory P consists of,

 - for each object p : obj P, a type of objects over c, denoted obj[p],

 - for each morphism f : a → b in P, x : obj[a] and y : obj[b] form a set of
   morphisms from x to y over f, denoted hom[f] x y,

 - for each p : obj P and x : obj[p], a morphism id : hom[id] x x, and

 - for all morphisms f : a → b and g : b → c in P and objects x : obj[a],
   y : obj[b], z : obj[c], a function
   
   ∘ : hom[g] y z → hom[f] x y → hom[f ○ g] x z.


Such that the following hold

- f ∘ id = id
- id ∘ f = f
- f ∘ (g ∘ h) = (f ∘ g) ∘ h 

\begin{code}

record DisplayedPrecategory (𝓦 𝓣 : Universe)
                            (P : Precategory 𝓤 𝓥)
                          : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓥)⁺ ̇  where
 open PrecategoryNotation P
 field
  obj[_] : (c : obj P) → 𝓦 ̇
  hom[_] : {a b : obj P}
           (f : hom a b)
           (x : obj[ a ])
           (y : obj[ b ])
         → 𝓣 ̇
  hom[-]-is-set : {a b : obj P}
                  {f : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                → is-set (hom[ f ] x y)
  
  D-𝒊𝒅 : {c : obj P}
         {x : obj[ c ]}
       → hom[ 𝒊𝒅 ] x x

  _○_ : {a b c : obj P}
         {g : hom b c}
         {f : hom a b}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {z : obj[ c ]}
         (gyz : hom[ g ] y z)
         (fxy : hom[ f ] x y)
       → hom[ g ◦ f ] x z

 private
  hom[-] : {a b : obj P}
            (x : obj[ a ])
            (y : obj[ b ])
          → hom a b → 𝓣 ̇
  hom[-] x y = λ - → hom[ - ] x y

 field
  D-𝒊𝒅-is-right-neutral : {a b : obj P}
                          {f' : hom a b}
                          {x : obj[ a ]}
                          {y : obj[ b ]}
                          (f : hom[ f' ] x y)
                        → f ○ D-𝒊𝒅 ＝⟦ hom[-] x y , 𝒊𝒅-is-right-neutral f' ⟧ f

  D-𝒊𝒅-is-left-neutral : {a b : obj P}
                         {f' : hom a b}
                         {x : obj[ a ]}
                         {y : obj[ b ]}
                         (f : hom[ f' ] x y)
                       → D-𝒊𝒅 ○ f ＝⟦ hom[-] x y , 𝒊𝒅-is-left-neutral f' ⟧ f
  
  D-assoc : {a b c d : obj P}
            {f' : hom a b}
            {g' : hom b c}
            {h' : hom c d}
            {x : obj[ a ]}
            {y : obj[ b ]}
            {z : obj[ c ]}
            {w : obj[ d ]}
            {f : hom[ f' ] x y}
            {g : hom[ g' ] y z}
            {h : hom[ h' ] z w}
          → h ○ (g ○ f)
          ＝⟦ hom[-] x w , assoc f' g' h' ⟧
            (h ○ g) ○ f

\end{code}

We can now define a displayed version of isomorphism between objects.

\begin{code}

 D-inverse : {p q : obj P}
             {d : obj[ p ]}
             {d' : obj[ q ]}
             (f : p ≅ q)
             (𝕗 : hom[ ⌜ f ⌝ ] d d')
           → 𝓣 ̇
 D-inverse {q} {p} {d} {d'} f 𝕗
   = Σ 𝕗⁻¹ ꞉ hom[ ⌞ underlying-morphism-is-isomorphism f ⌟ ] d' d
     , ((𝕗⁻¹ ○ 𝕗 ＝⟦ hom[-] d d , i ⟧ D-𝒊𝒅)
     × (𝕗 ○ 𝕗⁻¹ ＝⟦ hom[-] d' d' , ii ⟧ D-𝒊𝒅))
  where
   i = ⌞ underlying-morphism-is-isomorphism f ⌟-is-left-inverse
   ii = ⌞ underlying-morphism-is-isomorphism f ⌟-is-right-inverse

 _≅[_]_ : {p q : obj P}
          (d : obj[ p ])
          (f : p ≅ q)
          (d' : obj[ q ])
        → 𝓣 ̇
 d ≅[ f ] d' = Σ 𝕗 ꞉ hom[ ⌜ f ⌝ ] d d' , D-inverse f 𝕗
       
\end{code}

Following the definition of isomorphism, as with categories we can now define
the notion of id-to-iso for displayed precategories.

\begin{code}

 D-id-to-iso : {p q : obj P}
               (e : p ＝ q)
               (d : obj[ p ])
               (d' : obj[ q ])
               (e' : d ＝⟦ obj[_] , e ⟧ d')
             → d ≅[ id-to-iso p q e ] d'
 D-id-to-iso refl d _ refl = D-𝒊𝒅 , D-𝒊𝒅 , h , h
  where
   h : D-𝒊𝒅 ○ D-𝒊𝒅 ＝⟦ hom[-] d d , 𝒊𝒅-is-left-neutral 𝒊𝒅 ⟧ D-𝒊𝒅
   h = D-𝒊𝒅-is-left-neutral D-𝒊𝒅

\end{code}
