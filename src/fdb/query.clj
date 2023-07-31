(ns fdb.query
  [:use [fdb constructs]
        [clojure.set :as CS :only (intersection)]])

(defn variable?
  "A predicate that accepts a string and checks whether it describes a datalog variable (either starts with ? or it is _)"
  ([x] (variable? x true))
  ([x accept_?]                                             ; intentionally accepts a string and implemented as function and not a macro so we'd be able to use it as a HOF
   (or (and accept_? (= x "_")) (= (first x) \?))))

(defmacro clause-term-meta [clause-term]
  (cond
    (coll? clause-term) (first (filter #(variable? % false) (map str clause-term)))
    (variable? (str clause-term) false) (str clause-term)
    :no-variable-in-clause nil))

(defmacro clause-term-expr [clause-term]
  (cond
    (variable? (str clause-term))                           ;variable
    #(= % %)
    (not (coll? clause-term))                               ;constant
    `#(= % ~clause-term)
    (= 2 (count clause-term))                               ;unary operator
    `#(~(first clause-term) %)
    (variable? (str (second clause-term)))                  ;binary operator, 1st operand is variable
    `#(~(first clause-term) % ~(last clause-term))
    (variable? (str (last clause-term)))                    ;binary operator, 2nd operand is variable
    `#(~(first clause-term) ~(second clause-term) %)))

(defmacro pred-clause [clause]
  (loop [[trm# & rst-term#] clause exprs# [] metas# []]
    (if trm#
      (recur rst-term# (conj exprs# `(clause-term-expr ~ trm#))
             (conj metas# `(clause-term-meta ~ trm#)))
      (with-meta exprs# {:db/variable metas#}))))

(defmacro q-clauses-to-pred-clauses [clauses]
  (loop [[frst# & rst#] clauses preds-vecs# []]
    (if-not frst# preds-vecs#
                  (recur rst# `(conj ~preds-vecs# (pred-clause ~frst#))))))

(defn filter-index [index predicate-clauses]
  (for [pred-clause predicate-clauses
        :let [[lvl1-prd lvl2-prd lvl3-prd] (apply (from-eav index) pred-clause)]
        [k1 l2map] index                                    ;keys and values of the first level
        :when (try (lvl1-prd k1) (catch Exception e false))

        [k2 l3-set] l2map                                   ;keys and values of the second level
        :when (try (lvl2-prd k2) (catch Exception e false))
        :let [res (set (filter lvl3-prd l3-set))] ]
    (with-meta [k1 k2 res] (meta pred-clause))))

(defn items-that-answer-all-conditions [items-seq num-of-conditions]
  (->> items-seq                                            ;take the items-seq
       (map vec)                                            ;make each collection (actually a set) into a vector
       (reduce into [])                                     ;reduce all the vectors into one vector
       (frequencies)                                        ;count for each item in how many collections (sets) it was in
       (filter #(<= num-of-conditions (last %)))            ;items that answered all conditions
       (map first)                                          ;take from the duos the items themselves
       (set)))                                              ;return it as set

(defn mask-path-leaf-with-items [relevant-items path]
  (update-in path [2] CS/intersection relevant-items))

(defn combine-path-and-meta [from-eav-fn path]
  (let [expanded-path [(repeat (first path)) (repeat (second path)) (last path)]
        meta-of-path (apply from-eav-fn (map repeat (:db/variable (meta path))))
        combined-data-and-meta-path (interleave meta-of-path expanded-path)]
    (apply (partial map vector) combined-data-and-meta-path)))

(defn bind-variables-to-query [q-res index]
  (let [seq-res-path (mapcat (partial combine-path-and-meta (from-eav index))
                             q-res)
        res-path (map #(->> %1 (partition 2) (apply (to-eav index))) seq-res-path)]
    (reduce #(assoc-in %1 (butlast %2) (last %2)) {} res-path)))

(defn query-index [index pred-clauses]
  (let [result-clauses (filter-index index pred-clauses)
        relevant-items (items-that-answer-all-conditions (map last result-clauses)
                                                         (count pred-clauses))
        cleaned-result-clauses (map (partial mask-path-leaf-with-items
                                             relevant-items)
                                    result-clauses)]
    (filter #(not-empty (last %)) cleaned-result-clauses)))

(defn single-index-query-plan [query indx db]
  (let [q-res (query-index (indx-at db indx) query)]
    (bind-variables-to-query q-res (indx-at db indx))))

(defn index-of-joining-variable [query-clauses]
  (let [metas-seq (map #(:db/variable (meta %)) query-clauses)
        collapsing-fn (fn [accV v] (map #(when (= %1 %2) %1) accV v))
        collapsed (reduce collapsing-fn metas-seq)]
    (first (keep-indexed #(when (variable? %2 false) %1) collapsed))))

(defn build-query-plan [query]
  (let [term-ind (index-of-joining-variable query)
        ind-to-use (case term-ind 0 :AVET 1 :VEAT 2 :EAVT)]
    (partial single-index-query-plan query ind-to-use)))

(defn resultify-bind-pair [vars-set accum pair]
  (let [[ var-name _] pair]
    (if (contains? vars-set var-name) (conj accum pair) accum)))

(defn resultify-av-pair [vars-set accum-res av-pair]
  (reduce (partial resultify-bind-pair vars-set) accum-res av-pair))

(defn locate-vars-in-query-res [vars-set q-res]
  (let [[e-pair av-map] q-res
        e-res (resultify-bind-pair vars-set [] e-pair)]
    (map (partial resultify-av-pair vars-set e-res) av-map)))

(defn unify [binded-res-col needed-vars]
  (map (partial locate-vars-in-query-res needed-vars) binded-res-col))

(defmacro symbol-col-to-set [coll] (set (map str coll)))

(defmacro q
  [db query]
  `(let [pred-clauses# (q-clauses-to-pred-clauses ~(:where query))
         needed-vars# (symbol-col-to-set ~(:find query))
         query-plan# (build-query-plan pred-clauses#)
         query-internal-res# (query-plan# ~db)]
     (unify query-internal-res# needed-vars#)))



