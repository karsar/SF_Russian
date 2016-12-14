(** * Отображения: Тотальные и Частичные Отображения *)

(** Отображения (или словари) повсеместно встречающиеся структуры
    данных, как созданнии программного обеспечения вообщем, так и
    в теории языков программирования в частности. Нам они понадобятся
    во многих местах в дальнейших главах. Они также служат хорошим
    примером для использования идей из предыдущих глав, включая
    построение структур данных из функций высшего порядка (из [Basics] и
    [Poly]) и использования рефлексии для упрощения доказательств (из
    [IndProp]).

    Мы определим два вида отображений: _тотальные_ отображения, которые
    включают элемент "по умолчанию" для возвращения когда ключ который
    мы ищем не существует, и _частичные_ отображения, которые возвращают 
    [option] чтобы показать успех или неудачу. Последний вид определен
    в терминах предыдущего, используя [None] как элемент по умолчанию. *)

(* ################################################################# *)
(** * Стандартная Библиотека Coq *)

(** Одно небольшое ответвление перед началом.

    В отличие от глав что мы видели до сих пор, эта не требует
    [Require Import] для предыдущей главы (и, транзитивном всех предыдущих
    глав). Вместо этого, в данной главе и с этой главы, мы будем
    импортировать нужные определения и теоремы из стандарной библиотеки
    Coq.  Вы не должны заметить особой разницы, так как мы называли наши
    собственные определения и теоремы также как их аналоги из
    стандарной библиотеки, в тех случаях когда они пересекалис. *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

(** Документация для стандарной библиотеки может быть найдена в
    http://coq.inria.fr/library/.  

    Команда [SearchAbout] является хорошим способом искать теоремы
    включающие обьекты конкреных типов. *)

(* ################################################################# *)
(** * Идентификаторы *)

(** Во первых, нам нужен тип для ключей которые мы используем для
    индексирования наших отображений. Для этой цели, мы снова
    используем тип [id] из главы. Чтобы сделать данную главу
    самостоятельной, мы повторим определение здесь, вместе с
    с функцией сравнения на равенство для [id] и ее фундаментальным
    свойством. *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

(** Следующее полезное свойство [beq_id] следует из аналогичной
    леммы о числах: *)

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

(** Аналогично: *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** Данный полезный вариант следует просто из переписывания: *)

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * Тотальные отображения *)

(** Нашей основной работой в данной главе будет построение определения
    частичных отображений, которые похожи на то что
    мы видели в главе [Lists], плюс дополнительные леммы об их 
    поведении.

    В этот раз, в отличие, мы будем использовать _функции_, а не
    списки пар ключ-значение, для построения отображений. Преимущество
    такого представления в том, что оно представлает более _расширяемый_ 
    взгляд на отображения, где да отображения отвечающие на запросы
    тем же результатом будут представлены буквально как одно и тоже
    (таже функция), вместо просто "эквивалентных" структур данных.
    Это, в свою очередь, упрощает доказательства которые используют
    отображения.

    Мы строим частичные отображения в два шага. Во первых, мы определям тип
    _тотальных отображений (total maps)_ который возвращает значение по умолчанип
    в случае если ключ не представлен в отображении. *)

Definition total_map (A:Type) := id -> A.

(** Очевидно, тотальное отображение над элементом типа [A] _всего лишь_
    функция, которая может быть использована для поиска [id], производя [A].

    Функция [t_empty] производит пустое тотальное отображение, получив
    элемент для выдачи по умолчанию. Это отбражение всегда выдает лишь
    элемент по умолчанию когда к чему либо применена. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** Более интересна функция [update], которая (как и раньше) принимает
    отображение [m], ключ [x], и значение [v] и возвращает новое отображение
    которое при [x] выдает [v] и для остальных аргументов предоставляет тот
    эе результат, что и [m]. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

(** Это определние является хорошим примером программирования
    высшего порядка. Функция [t_update] принимает _функцию_ [m] 
    и производит новую функцию [fun x' => ...] которая ведет себя
    как нужное отображение.

    Например, мы можем построить отображение переводящее [id] в [bool]s,
    где [Id 3] отображено в [true] и каждый другой ключ отображен в [false]: *)

Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

(** Этим мы завершаем определение тотальных отображений. Заметьте, что
    нам не надо определять операцию поиска [find] так как это просто
    применение функции! *)

Example update_example1 : examplemap (Id 0) = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id 1) = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id 2) = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id 3) = true.
Proof. reflexivity. Qed.

(** Для использования отображений в последующих главах нам необходимо
    несколько фундаментальных фактов об их поведении. Даже если вы
    не проработаете следующие упражнения, убедитесь что вы хорошо
    понимаете утверждения в леммах!  (Некоторые из доказательств
    требуют аксиомы расширяемости, которая была обсуждена в главе
    [Logic] и включена в стандартную библиотеку Coq.) *)

(** **** Упражнение: 1 звездочка, дополнительное (t_apply_empty)  *)
(** Во первых, пустое отображение возвращает свой элемент по умолчанию для всех ключей: *)
Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звезздочки, дополнительное (t_update_eq)  *)
(** Далее, если вы обновите отображение [m] для ключа [x] новым значением [v]
    а затем поищете для [x] в результирующем отображении после [update],
    вы получите обратно [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звездочки, дополнительное (t_update_neq)  *)
(** С другой сторомы, если мы обновим отображение [m] в ключе [x1], а
    затем поищем для _другого_ ключа [x2] в результирующем отображении, 
    мы получим тот же результат, который был бы предоставлен отображением
    [m]: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *)
 Admitted.
(** [] *)

(** **** Упражнение: 2 звездочки, дополнительное (t_update_shadow)  *)
(** Если мы обновим отображение [m] для ключа [x] со значением [v1] и
    затем снова для данного ключа и с другим значением [v2], результирующее
    отображение ведет себя также (предоставляет тот же результат
    для любого ключа) как и более простое отображение полученое
    просто с одним вторым обновлением [update] на [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЪ *) Admitted.
(** [] *)

(** Для последних двух лемм о тотальных отображениях, удобно
    использовать идиому рефлексии введеную в главе [IndProp]. Мы начнем
    с доказательства фундаментальной _леммы о рефлексии_ связывающей пропозицию
    равенства для [id] с булевой функцией [beq_id]. *)

(** **** Упражнение: 2 звездочки (beq_idP)  *)
(** Используйте доказательство [beq_natP] из главы [IndProp] как шаблон
    для доказательства следующего: *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** [] *)

(** Теперь, имея [id]торы [x1] и [x2], мы можем использовать [destruct (beq_idP
    x1 x2)] для одновременного анализа случаев на результате
    [beq_id x1 x2] и генерации гипотез о равенствах (в смысле
    [=]) для [x1] и [x2]. *)

(** **** Упражнение: 2 звездочки (t_update_same)  *)
(** Используя пример из главы [IndProp] как шаблон, воспользуйтесь
    [beq_idP] для доказательства следующих теорем, которые утверждают
    что если мы обновим отображение так чтобы присвоить [x] тоже значение,
    что он и так имеет в [m], то результат будет равен [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звездочки, рекомендованное (t_update_permute)  *)
(** Используйте [beq_idP] для доказательства последнего свойства функции [update].
    Если мы обновим отображение [m] для двух разных ключей, то не имеет значение
    в каком порядке мы это сделаем. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ*) Admitted.
(** [] *)

(* ################################################################# *)
(** * Частичные отображения *)

(** Наконевц, мы определяем _частичные отображения_ на основе тотальных отображений.
    Частичное отображение из типа [A] есть просто тотальное отображение с элементами
    типа [option A] и элементом по умолчанию [None]. *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

(** Мы можем поднять все наши базовые леммы из тотальных отображений
    до частичных.  *)

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

(** $Date: 2015-12-11 17:17:29 -0500 (Fri, 11 Dec 2015) $ *)

