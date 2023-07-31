;(ns fdb.constructs
;  (:use fdb.storage)
;  (:import [fdb.storage.InMemory]))
;
;(defrecord Database [layers top-id curr-time])
;(defrecord Layer [storage VAET AVET VEAT EAVT])
;
;(defrecord Entity [id attrs])
;
;(defn make-entity
;  ([] (make-entity :db/no-id-yet))
;  ([id] (Entity. id {})))
;
;
;(defrecord Attr [name value ts prev-ts])
;
;(defn make-attr
;  ([name value type ; these ones are required
;   & {:keys [cardinality] :or {cardinality :db/single}} ]
;   {:pre [(contains? #{:db/single :db/multiple} cardinality)]}
;   (with-meta (Attr. name value -1 -1) {:type type :cardinality cardinality})))
;
;(defn add-attr [ent attr]
;  (let [attr-id (keyword (:name attr))]
;    (assoc-in ent [:attrs attr-id] attr)))
;
;(defprotocol Storage
;  (get-entity [storage e-id])
;  (write-entity [storage entity])
;  (drop-entity [storage entity]))
;
;(defrecord  [] Storage
;  (get-entity [storage e-id] (e-id storage))
;  (write-entity [storage entity] (assoc storage (:id entity) entity))
;  (drop-entity [storage entity] (dissoc storage (:id entity))))
;
;(defn make-index [from-eav to-eav usage-pred]
;  (with-meta {} {:from-eav from-eav :to-eav to-eav :usage-pred usage-pred}))
;
;(defn from-eav [index] (:from-eav (meta index)))
;(defn to-eav [index] (:to-eav (meta index)))
;(defn usage-pred [index] (:usage-pred (meta index)))
;
;(defn indexes [] [:VAET :AVET :VEAT :EVAT])
;
;(defn ref? [attr] (= :db/ref (:type (meta attr))))
;
;(defn always [& more] true)
;
;(defn make-db []
;  (atom
;    (Database. [(Layer.
;                  (fdb.storage.InMemory.)                   ; storage
;                  (make-index #(vector %3 %2 %1) #(vector %3 %2 %1) #(ref? %)) ;VAET
;                  (make-index #(vector %2 %3 %1) #(vector %3 %1 %2) always) ;AVET
;                  (make-index #(vector %3 %1 %2) #(vector %2 %3 %1) always) ;VEAT
;                  (make-index #(vector %1 %2 %3) #(vector %1 %2 %3) always) ;EAVT
;                  )] 0 0)))
;
;(defn entity-at
;  ([db ent-id] (entity-at db (:curr-time db) ent-id))
;  ([db ts ent-id] (get-entity (get-in db [:layers ts :storage]) ent-id)))
;(defn attr-at
;  ([db ent-id attr-name] (attr-at db ent-id attr-name (:curr-time db)))
;  ([db ent-id attr-name ts] (get-in (entity-at db ts ent-id) [:attrs attr-name])))
;(defn value-of-at
;  ([db ent-id attr-name] (:value (attr-at db ent-id attr-name)))
;  ([db ent-id attr-name ts] (:value (attr-at db ent-id attr-name ts))))
;(defn indx-at
;  ([db kind] (indx-at db kind (:curr-time db)))
;  ([db kind ts] (kind ((:layers db) ts))))
;
;(defn evolution-of [db ent-id attr-name]
;  (loop [res [] ts (:curr-time db)]
;    (if (= -1 ts) (reverse res)
;                  (let [attr (attr-at db ent-id attr-name ts)]
;                    (recur (conj res {(:ts attr) (:value attr)}) (:prev-ts attr))))))
;
;
;(defn add-entity [db ent]
;  (let [[fixed-ent next-top-id] (fix-new-entity db ent)
;        layer-with-updated-storage (update-in
;                                     (last (:layers db)) [:storage] write-entity fixed-ent)
;        add-fn (partial add-entity-to-index fixed-ent)
;        new-layer (reduce add-fn layer-with-updated-storage (indexes))]
;    (assoc db :layers (conj (:layers db) new-layer) :top-id next-top-id)))
;
;(defn- next-ts [db] (inc (:curr-time db)))
;
;(defn- update-creation-ts [ent ts-val]
;  (reduce #(assoc-in %1 [:attrs %2 :ts ] ts-val) ent (keys (:attrs ent))))
;
;(defn- next-id [db ent]
;  (let [top-id (:top-id db)
;        ent-id (:id ent)
;        increased-id (inc top-id)]
;    (if (= ent-id :db/no-id-yet)
;      [(keyword (str increased-id)) increased-id]
;      [ent-id top-id])))
;
;(defn- fix-new-entity [db ent]
;  (let [[ent-id next-top-id] (next-id db ent)
;        new-ts (next-ts db)]
;    [(update-creation-ts (assoc ent :id ent-id) new-ts) next-top-id]))
;
;(defn- add-entity-to-index [ent layer ind-name]
;  (let [ent-id (:id ent)
;        index (ind-name layer)
;        all-attrs (vals (:attrs ent))
;        relevant-attrs (filter #((usage-pred index) %) all-attrs)
;        add-in-index-fn (fn [ind attr]
;                          (update-attr-in-index ind ent-id (:name attr)
;                                                (:value attr)
;                                                :db/add))]
;    (assoc layer ind-name (reduce add-in-index-fn index relevant-attrs))))
;
;(defn- update-attr-in-index [index ent-id attr-name target-val operation]
;  (let [colled-target-val (collify target-val)
;        update-entry-fn (fn [ind vl]
;                          (update-entry-in-index
;                            ind
;                            ((from-eav index) ent-id attr-name vl)
;                            operation))]
;    (reduce update-entry-fn index colled-target-val)))
;
;(defn- update-entry-in-index [index path operation]
;  (let [update-path (butlast path)
;        update-value (last path)
;        to-be-updated-set (get-in index update-path #{})]
;    (assoc-in index update-path (conj to-be-updated-set update-value))))
;
;(defn add-entities [db ents-seq] (reduce add-entity db ents-seq))
;
;(defn remove-entity [db ent-id]
;  (let [ent (entity-at db ent-id)
;        layer (remove-back-refs db ent-id (last (:layers db)))
;        no-ref-layer (update-in layer [:VAET] dissoc ent-id)
;        no-ent-layer (assoc no-ref-layer :storage
;                                         (drop-entity
;                                           (:storage no-ref-layer) ent))
;        new-layer (reduce (partial remove-entity-from-index ent)
;                          no-ent-layer (indexes))]
;    (assoc db :layers (conj (:layers db) new-layer))))
;
;(defn- remove-back-refs [db e-id layer]
;  (let [reffing-datoms (reffing-to e-id layer)
;        remove-fn (fn [d [e a]] (update-entity db e a e-id :db/remove))
;        clean-db (reduce remove-fn db reffing-datoms)]
;    (last (:layers clean-db))))
;
;(defn- reffing-to [e-id layer]
;  (let [vaet (:VAET layer)]
;    (for [[attr-name reffing-set] (e-id vaet)
;          reffing reffing-set]
;      [reffing attr-name])))
;
;
;(defn update-entity
;  ([db ent-id attr-name new-val]
;   (update-entity db ent-id attr-name new-val :db/reset-to))
;  ([db ent-id attr-name new-val operation]
;   (let [update-ts (next-ts db)
;         layer (last (:layers db))
;         attr (attr-at db ent-id attr-name)
;         updated-attr (update-attr attr new-val update-ts operation)
;         fully-updated-layer (update-layer layer ent-id
;                                           atr updated-attr
;                                           new-val operation)]
;     (update-in db [:layers] conj fully-updated-layer))))
;
;(defn- update-attr [attr new-val new-ts oepration]
;  {:pre [(if (single? attr)
;           (contains? #{:db/reset-to :db/remove} operation)
;           (contains? #{:db/reset-to :db/add :db/remove} operation))]}
;  (-> attr
;      (update-attr-modification-time new-ts)
;      (update-attr-value new-val operaiton)))
;
;(defn- update-attr-modification-time
;  [attr new-ts]
;  (assoc attr :ts new-ts :prev-ts (:ts attr)))
;
;(defn- update-attr-value [attr value operation]
;  (cond
;    (single? attr) (assoc attr :value #{value})
;    ;now we're talking about an attribute of multiple values
;    (= :db/reset-to operation)
;    (assoc attr :value value)
;    (= :db/add operation)
;    (assoc attr :value (CS/union (:value attr) value))
;    (= :db/remove operation)
;    (assoc attr :value (CS/difference (:value attr) value))))
;
;(defn transact-on-db [initial-db ops]
;  (loop [[op & rst-ops] ops transacted initial-db]
;    (if op
;      (recur rst-ops (apply (first op) transacted (rest op)))
;      (let [initial-layer (:layers initial-db)
;            new-layer (last (:layers transacted))]
;        (assoc initial-db :layers (conj initial-layer new-layer)
;                          :curr-time (next-ts initial-db)
;                          :top-id (:top-id transacted))))))
;
;(defmacro transact [db-conn & txs] `(_transact ~db-conn swap! ~@txs))
;
;(defmacro _transact [db op & txs]
;  (when txs
;    (loop [[frst-tx# & rst-tx#] txs res# [op db `transact-on-db] accum-txs# []]
;      (if frst-tx#
;        (recur rst-tx# res# (conj accum-txs# (vec frst-tx#)))
;        (list* (conj res# accum-txs#))))))
;
;(defmacro what-if [db & ops] `(_transact ~db _what-if ~@ops))
;
;(defn- _what-if [db f txs] (f db txs))
;
;(defn incoming-refs [db ts ent-id & ref-names]
;  (let [vaet (indx-at db :VAET ts)
;        all-attr-map (vaet ent-id)
;        filtered-map (if ref-names
;                       (select-keys ref-names all-attr-map)
;                       all-attr-mao)]
;    (reduce into #{} (vals filtered-map))))
;
;(defn outgoing-refs [db ts ent-id & ref-names]
;  (let [val-filter-fn (if ref-names #(vals (select-keys ref-names %)) vals)]
;    (if-not ent-id []
;                   (->> (entity-at db ts ent-id)
;                        (:attrs) (val-filter-fn) (filter ref?) (mapcat :value)))))
;
;(defmacro symbol-col-to-set [coll] (set (map str coll)))
;
;(defmacro clause-term-expr [clause-term]
;  (cond
;    (variable? (str clause-term))                           ;variable
;    #(= % %)
;    (not (coll? clause-term))                               ;constant
;    `#(= % ~clause-term)
;    (= 2 (count clause-term))                               ;unary operator
;    `#(~(first clause-term) %)
;    (variable? (str (second clause-term)))                  ;binary operator, 1st operand is variable
;    `#(~(first clause-term) % ~(last clause-term))
;    (variable? (str (last clause-term)))                    ;binary operator, 2nd operand is variable
;    `#(~(first clause-term) ~(second clause-term) %)))
;
;(defmacro clause-term-meta [clause-term]
;  (cond
;    (coll? clause-term) (first (filter #(variable? % false) (map str clause-term)))
;    (variable? (str clause-term) false) (str clause-term)
;    :no-variable-in-clause nil))
;
;(defmacro pred-clause [clause]
;  (loop [[trm# & rst-term#] clause expres# [] metas# []]
;    (if trm#
;      (recur rst-trm# (conj exprs# `(clause-term-expr ~ trm#))
;             (conj metas# `(clause-term-meta ~ trm#)))
;      (with-meta exprs# {:db/variable metas#}))))
;
;(defmacro q-clauses-to-pred-clauses [clauses]
;  (loop [[frst# & rst#] clauses preds-vecs# []]
;    (if-not frst# preds-vecs#
;                  (recur rst# `(conj ~preds-vecs# (pred-clause ~frst#))))))
;
;
;(defn index-of-joining-variable [query-clauses]
;  (let [metas-seq (map #(:db/variable (meta %)) query-clauses)
;        collapsing-fn (fn [accV v] (map #(when (= %1 %2) %1) accV v))
;        collapsed (reduce collapsing-fn metas-seq)]
;    (first (keep-indexed #(when (variable? %2 false) %1) collapsed))))
;
;(defn build-query-plan [query]
;  (let [term-ind (index-of-joining-variable query)
;        ind-to-use (case term-ind 0 :AVET 1 :VEAT 2 :EAVT)]
;    (partial single-index-query-plan query ind-to-use)))
;
;(defn single-index-query-plan [query indx db]
;  (let [q-res (query-index (indx-at db indx) query)]
;    (bind-variables-to-query q-res (indx-at db indx))))
;
;(defn query-index [index pred-clauses]
;  (let [result-clauses (filter-index index pred-clauses)
;        relevant-items (items-that-answer-all-conditions (map last result-clauses)
;                                                         (count pred-clauses))
;        cleaned-result-clauses (map (partial mask-path-leaf-with-items
;                                             relevant-items)
;                                    result-clauses)]
;    (filter #(not-empty (last %)) cleaned-result-clauses)))
;
;(defn filter-index [index predicate-clauses]
;  (for [pred-clause predicate-clauses
;        :let [[lvl1-prd lvl2-prd lvl3-prd] (apply (from-eav index) pred-clause)]
;        [k1 l2map] index                                    ;keys and values of the first level
;        :when (try (lvl1-prd k1) (catch Exception e false))
;
;        [k2 l3-set] l2map                                   ;keys and values of the second level
;        :when (try (lvl2-prd k2) (catch Exception e false))
;        :let [res (set (filter lvl3-prd l3-set))] ]
;    (with-meta [k1 k2 res] (meta pred-clause))))
;
;(defn items-that-answer-all-conditions [items-seq num-of-conditions]
;  (->> items-seq                                            ;take the items-seq
;       (map vec)                                            ;make each collection (actually a set) into a vector
;       (reduce into [])                                     ;reduce all the vectors into one vector
;       (frequencies)                                        ;count for each item in how many collections (sets) it was in
;       (filter #(<= num-of-conditions (last %)))            ;items that answered all conditions
;       (map first)                                          ;take from the duos the items themselves
;       (set)))                                              ;return it as set
;
;(defn mask-path-leaf-with-items [relevant-items path]
;  (update-in path [2] CS/intersection relevant-items))
;
;(defn bind-variables-to-query [q-res index]
;  (let [seq-res-path (mapcat (partial combine-path-and-meta (from-eav index))
;                             q-res)
;        res-path (map #(->> %1 (partition 2) (apply (to-eav index))) seq-res-path)]
;    (reduce #(assoc-in %1 (butlast %2) (last %2)) {} res-path)))
;
;(defn combine-path-and-meta [from-eav-fn path]
;  (let [expanded-path [(repeat (first path)) (repeat (second path)) (last path)]
;        meta-of-path (apply from-eav-fn (map repeat (:db/variable (meta path))))
;        combined-data-and-meta-path (interleave meta-of-path expanded-path)]
;    (apply (partial map vector) combined-data-and-meta-path)))
;
;(defn unify [binded-res-col needed-vars]
;  (map (partial locate-vars-in-query-res needed-vars) binded-res-col))
;
;(defn locate-vars-in-query-res [vars-set q-res]
;  (let [[e-pair av-map] q-res
;        e-res (resultify-bind-pair vars-set [] e-pair)]
;    (map (partial resultify-av-pair vars-set e-res) av-map)))
;
;(defn resultify-bind-pair [vars-set accum pair]
;  (let [[ var-name _] pair]
;    (if (contains? vars-set var-name) (conj accum pair) accum)))
;
;(defn resultify-av-pair [vars-set accum-res av-pair]
;  (reduce (partial resultify-bind-pair vars-set) accum-res av-pair))
;
;(defmacro q
;  [db query]
;  `(let [pred-clauses# (q-clauses-to-pred-clauses ~(:where query))
;         needed-vars# (symbol-col-to-set ~(:find query))
;         query-plan# (build-query-plan pred-clauses#)
;         query-internal-res# (query-plan# ~db)]
;     (unify query-internal-res# needed-vars#)))
;
;
;
