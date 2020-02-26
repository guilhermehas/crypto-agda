\begin{code}
data Result {A : Set} : A → Set where
  res : (x : A) → Result x
\end{code}

%<*Id>
\begin{code}
id : {A : Set} → A → A
id = λ x → x
\end{code}
%</Id>

%<*Id2>
\begin{code}
id' : {A : Set} → A → A
id' x = x
\end{code}
%</Id2>

%<*trueFalse>
\begin{code}
true : {A : Set} → A → A → A
true x y = x

false : {A : Set} → A → A → A
false x y = y
\end{code}
%</trueFalse>

%<*naturals>
\begin{code}
zero : {A : Set} → (A → A) → A → A
zero suc z = z

one : {A : Set} → (A → A) → A → A
one suc z = suc z

two : {A : Set} → (A → A) → A → A
two suc z = suc (suc z)
\end{code}
%</naturals>

%<*isZero>
\begin{code}
isZero : {A : Set} → ((A → A) → A → A) → (A → A → A)
isZero n true false = n (λ _ → false) true

isZero-zero : {A : Set} → Result (isZero {A} zero)
isZero-zero = res (λ true false → true)

isZero-two : {A : Set} → Result (isZero {A} two)
isZero-two = res (λ true false → false)
\end{code}
%</isZero>

%<*plus>
\begin{code}
plus : {A : Set} → ((A → A) → A → A)
  → ((A → A) → A → A)
  → ((A → A) → A → A)
plus n m = λ suc z → n suc (m suc z)

_+_ : {A : Set} → ((A → A) → A → A)
  → ((A → A) → A → A)
  → ((A → A) → A → A)
_+_ n m suc z = n suc (m suc z)
\end{code}
%</plus>

%<*onePone>
\begin{code}
one+one : {A : Set} → Result (_+_ {A} one one)
one+one = res (λ suc z → suc (suc z))
\end{code}
%</onePone>

%<*list>
\begin{code}
emptyList : {A List : Set}
  → (A → List → List) → List → List
emptyList _::_ nil = nil

natList : {A List : Set}
  → (((A → A) → A → A) → List → List) → List → List
natList _::_ nil = one :: (two :: nil)
\end{code}
%</list>

%<*sumList>
\begin{code}
sumList : {A List : Set}
  → Result (natList {A} {(A → A) → A → A} _+_ zero)
sumList = res (λ suc z → suc (suc (suc z)))
\end{code}
%</sumList>

%<*either>
\begin{code}
left : {A B C : Set} → A → (A → C) → (B → C) → C
left x f g = f x

right : {A B C : Set} → B → (A → C) → (B → C) → C
right x f g = g x
\end{code}
%</either>

%<*eitherExamples>
\begin{code}
zero-left : ∀ {A B C}
  → (((A → A) → A → A) → C) → (B → C) → C
zero-left = left zero

one-left : ∀ {A B C}
  → (((A → A) → A → A) → C) → (B → C) → C
one-left = left one

false-right : ∀ {A B C}
  → (A → C) → ((B → B → B) → C) → C
false-right = right false

true-right :  ∀ {A B C}
  → (A → C) → ((B → B → B) → C) → C
true-right = right true
\end{code}
%</eitherExamples>

%<*eitherRes>
\begin{code}
zero-isZero : ∀ {A}
  → Result (zero-left {A} isZero id)
zero-isZero = res (λ true false → true)

one-isZero : ∀ {A}
  → Result (one-left {A} isZero id)
one-isZero = res (λ true false → false)

false-id : ∀ {A}
  → Result (false-right {(A → A) → A → A} isZero id)
false-id = res (λ true false → false)

true-id : ∀ {A}
  → Result (false-right {(A → A) → A → A} isZero id)
true-id = res (λ true false → false)
\end{code}
%</eitherRes>

%<*tuple>
\begin{code}
tuple : {A B C : Set} → A → B → (A → B → C) → C
tuple x y f = f x y
\end{code}
%</tuple>

%<*tupleExamples>
\begin{code}
zero-false : {A B C : Set} → (((A → A) → A → A)
  → (B → B → B) → C) → C
zero-false = tuple zero false

one-true : {A B C : Set} → (((A → A) → A → A)
  → (B → B → B) → C) → C
one-true = tuple one true
\end{code}
%</tupleExamples>

%<*tupleAdd>
\begin{code}
add-true : {A : Set} → ((A → A) → A → A)
  → (A → A → A) → ((A → A) → A → A)
add-true n b suc z = b (suc (n suc z)) (n suc z)

add-zero-false : {A : Set}
  → Result (zero-false {(A → A) → A → A} add-true)
add-zero-false = res (λ suc z → z)

add-one-true : ∀ {A}
  → Result (one-true {(A → A) → A → A} add-true)
add-one-true = res (λ suc z → suc (suc z))
\end{code}
%</tupleAdd>
