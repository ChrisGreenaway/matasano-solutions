(ns crypto.core
  (:gen-class)
)

(require '[clojure.data.codec.base64 :as b64])
(require '[http.async.client :as http])
(require '[clojure.string :as string])
(require '[clojure.math.combinatorics :as combo])
(require '[clojure.walk :as walk])
(require '[clojure.contrib.seq :as seq])
(require '[clojure.math.numeric-tower :as math])

(defmacro dbg[x] `(let [x# ~x] (println "dbg:" '~x "=" x#) x#))

(defn byte-array-to-byte-list
  [ba]
  (apply list ba))

(defn list-to-byte-list
  [li]
  (map byte li))

(defn byte-list-to-byte-array
  [bl]
  (byte-array bl))

(defn string-to-bytes
  [s]
  (.getBytes s "UTF-8"))

(defn string-to-byte-list
  [s]
  (byte-array-to-byte-list (string-to-bytes s)))

(defn bytes-to-string
  [ba]
  (new String ba "UTF-8"))

(defn byte-list-to-string
  [bl]
  (bytes-to-string (byte-list-to-byte-array bl)))

(defn hex-string-to-bytes
  [s]
  (javax.xml.bind.DatatypeConverter/parseHexBinary s))

(defn hex-string-to-byte-list
  [s]
  (byte-array-to-byte-list (hex-string-to-bytes s)))

(defn base64-string-to-bytes
  [s]
  (b64/decode (string-to-bytes s)))

(defn base64-string-to-byte-list
  [s]
  (byte-array-to-byte-list (base64-string-to-bytes s)))

(defn bytes-to-hex-string
  [ba]
  (.toLowerCase (javax.xml.bind.DatatypeConverter/printHexBinary ba)))

(defn byte-list-to-hex-string
  [bl]
  (bytes-to-hex-string (byte-list-to-byte-array bl)))

(defn bytes-to-base64-string
  [ba]
  (bytes-to-string (b64/encode ba)))

(defn byte-list-to-base64-string
  [bl]
  (bytes-to-base64-string (byte-list-to-byte-array bl)))

(defn hex-string-to-base64-string
  [s]
  (bytes-to-base64-string (hex-string-to-bytes s)))

(defn base64-string-to-hex-string
  [s]
  (bytes-to-hex-string (base64-string-to-bytes s)))

(defn xor-bytes
  [& bytes]
  (byte (apply bit-xor bytes)))

(defn xor-byte-lists
  [bl1 bl2]
  (map #(xor-bytes (first %) (second %)) (map list bl1 bl2)))

(defn split-byte-list-every-n
  [n bl]
  (partition-all n bl))

(defn repeating-xor-cipher
  [key bl]
  (reduce concat
    (map #(xor-byte-lists key %)
      (split-byte-list-every-n (count key) bl))))

(defn byte-score
  [b]
  (+
    (if (and (>= b 32) (<= b 126))
      10
      0)
    (if (= b 32)
      10
      0)
    (if (and (>= b 65) (<= b 90))
      1
      0)
    (if (and (>= b 97) (<= b 122))
      5
      0)))

(defn message-score
  [bl]
  (reduce + (map byte-score bl)))

(defn byte-range
  []
  (map #(byte %)
    (concat
      (range 0 128)
      (range -128 0))))

(defn decipher-single-byte-xor
  [bl]
  (apply max-key message-score
    (map #(repeating-xor-cipher (list %) bl)
      (byte-range))))

(defn get-lines-from-url
  [url]
  (string/split-lines
    (with-open [client (http/create-client)]
      (let [response (http/GET client url)]
        (http/string (http/await (http/GET client url)))))))

(defn find-decryptable-hex-string
  [strings]
  (apply max-key message-score
    (map #(decipher-single-byte-xor (hex-string-to-byte-list %)) strings)))

(defn bit-count
  [b]
  (reduce +
    (map #(if (bit-test b %) 1 0)
      (range 0 8))))

(defn hamming-distance
  [bl1 bl2]
  (reduce +
    (map bit-count (xor-byte-lists bl1 bl2))))

(defn hamming-distance-string
  [s1 s2]
  (hamming-distance (string-to-bytes s1) (string-to-byte-list s2)))

(defn normalised-hamming-distance
  [bl1 bl2]
  (/ (hamming-distance bl1 bl2) (count bl1)))

(defn average
  [li]
  (/ (reduce + li) (count li)))

(defn average-normalised-hamming-distance
  [key-size bl]
  (average (take 10
    (map #(normalised-hamming-distance (first %) (second %))
      (combo/combinations (split-byte-list-every-n key-size bl) 2)))))

(defn xor-key-size
  [bl]
  (apply min-key #(average-normalised-hamming-distance % bl)
    (range 2 40)))

(def not-nil? (comp not nil?))

(defn map-longest
  [fn & colls]
  (lazy-seq
    (when (not-every? empty? colls)
      (let [firsts (filter not-nil? (map first colls))]
        (cons
          (apply fn firsts)
          (apply map-longest fn
            (map rest colls)))))))

(defn transpose
  [li]
  (apply map-longest list li))

(defn find-key-byte
  [bl]
  (first (xor-byte-lists bl (decipher-single-byte-xor bl))))

(defn find-multi-byte-xor-key-given-key-size
  [bl key-size]
  (map #(find-key-byte %)
    (transpose (split-byte-list-every-n key-size bl))))

(defn find-multi-byte-xor-key
  [bl]
  (find-multi-byte-xor-key-given-key-size bl (xor-key-size bl)))

(defn decipher-multi-byte-xor
  [bl]
  (repeating-xor-cipher (find-multi-byte-xor-key bl) bl))

(defn aes-decrypt
  [key cipher-text-ba]
  (let [cipher (javax.crypto.Cipher/getInstance "AES/ECB/NoPadding")]
    (.init cipher javax.crypto.Cipher/DECRYPT_MODE (new javax.crypto.spec.SecretKeySpec key "AES"))
    (.doFinal cipher cipher-text-ba)))

(defn aes-encrypt
  [key plain-text-ba]
  (let [cipher (javax.crypto.Cipher/getInstance "AES/ECB/NoPadding")]
    (.init cipher javax.crypto.Cipher/ENCRYPT_MODE (new javax.crypto.spec.SecretKeySpec key "AES"))
    (.doFinal cipher plain-text-ba)))

(defn index-of
  [item li]
  (first (seq/positions (partial = item) li)))

(defn duplicates
  [li]
  (map first
    (filter #(> (count (second %)) 1)
      (group-by identity li))))

(defn first-duplicate-index
  [li]
  (index-of (first (duplicates li)) li))

(defn duplicates?
  [li]
  ((comp not empty?) (duplicates li)))

(defn duplicate-blocks?
  [block-size bl]
  (duplicates? (split-byte-list-every-n block-size bl)))

(defn duplicate-16-byte-block?
  [bl]
  (duplicate-blocks? 16 bl))

(defn first-duplicate-block-index
  [block-size bl]
  (first-duplicate-index (split-byte-list-every-n block-size bl)))

(defn first-duplicate-16-byte-block-index
  [bl]
  (first-duplicate-block-index 16 bl))

(defn find-ecb-hex-strings
  [strings]
  (filter #(duplicate-16-byte-block? (hex-string-to-byte-list %)) strings))

(defn pad-with-pkcs7
  [block-size bl]
  (let [padding-size (- block-size (mod (count bl) block-size))]
    (concat bl (repeat padding-size (byte padding-size)))))

(defn between
  [low high x]
  (if (> low high)
    (between high low x)
    (and (>= x low) (<= x high))))

(defn remove-pkcs7-padding
  [block-size bl]
  (let [
    reverse-bl (reverse bl)
    padding-byte (first reverse-bl)
  ]
    (if
      (or
        (empty? bl)
        (> (mod (count bl) 16) 0)
        (not (between 1 16 padding-byte))
        (not (= (take padding-byte reverse-bl) (repeat padding-byte (byte padding-byte)))))
      (throw (Exception. "Invalid Padding"))
      (reverse (drop padding-byte reverse-bl)))))

(defn aes-encrypt-byte-list
  [key bl]
  (byte-array-to-byte-list
    (aes-encrypt
      (byte-list-to-byte-array key)
      (byte-list-to-byte-array bl))))

(defn aes-decrypt-byte-list
  [key bl]
  (byte-array-to-byte-list
    (aes-decrypt
      (byte-list-to-byte-array key)
      (byte-list-to-byte-array bl))))

(defn aes-cbc-encrypt
  [key iv plain-text]
  (let [block-size 16]
    (first
      (reduce
        (fn [cbc-data plain-text-block]
          (let [
            cipher-text (first cbc-data)
            previous-cipher-block (second cbc-data)
          ]
            (let [cipher-block (aes-encrypt-byte-list key (xor-byte-lists previous-cipher-block plain-text-block))]
              (list (concat cipher-text cipher-block) cipher-block))))
        (list () iv)
        (split-byte-list-every-n block-size (pad-with-pkcs7 block-size plain-text))))))

(defn aes-cbc-decrypt
  [key iv cipher-text]
  (let [block-size 16]
    (remove-pkcs7-padding block-size (first
      (reduce
        (fn [cbc-data cipher-text-block]
          (let [
            plain-text (first cbc-data)
            previous-cipher-block (second cbc-data)
          ]
            (let [plain-text-block (xor-byte-lists previous-cipher-block (aes-decrypt-byte-list key cipher-text-block))]
	      (list (concat plain-text plain-text-block) cipher-text-block))))
	(list () iv)
        (split-byte-list-every-n block-size cipher-text))))))

(defn random-byte-list
  [size]
  (byte-array-to-byte-list
    (let [result (byte-array size)]
      (.nextBytes (new java.security.SecureRandom) result)
      result)))

(defn random-int
  [n]
  (.nextInt (new java.security.SecureRandom) n))

(defn random-byte-list-random-length
  [a b]
  (random-byte-list (+ a (random-int (- b a)))))

(defn random-aes-key
  []
  (random-byte-list 16))

(defn random-iv
  []
  (random-byte-list 16))

(defn random-ecb-cbc-encrypt
  [bl]
  (let [
    key (random-aes-key)
    encrypt (if (zero? (random-int 2))
      #((partial aes-encrypt-byte-list key) (pad-with-pkcs7 16 %))
      (partial aes-cbc-encrypt key (random-iv)))
  ]
    (encrypt
      (concat (random-byte-list-random-length 5 11) bl (random-byte-list-random-length 5 11)))))

(defn zero-byte-list
  [size]
  (repeat size (byte 0)))

(defn is-ecb-or-cbc-encryption
  [encryption-function]
  (if (duplicate-16-byte-block? (encryption-function (zero-byte-list 64 )))
    "ECB"
    "CBC"))

(def random-but-known-key (random-aes-key))

(defn ecb-encrypt-with-hidden-extra-plain-text
  [plain-text]
  (aes-encrypt-byte-list random-but-known-key
    (pad-with-pkcs7 16
      (concat plain-text (base64-string-to-byte-list "Um9sbGluJyBpbiBteSA1LjAKV2l0aCBteSByYWctdG9wIGRvd24gc28gbXkgaGFpciBjYW4gYmxvdwpUaGUgZ2lybGllcyBvbiBzdGFuZGJ5IHdhdmluZyBqdXN0IHRvIHNheSBoaQpEaWQgeW91IHN0b3A/IE5vLCBJIGp1c3QgZHJvdmUgYnkK")))))

(def random-but-known-prefix (random-byte-list-random-length 4 36))

(defn ecb-encrypt-with-random-prefix-and-hidden-extra-plain-text
  [plain-text]
  (ecb-encrypt-with-hidden-extra-plain-text
    (concat random-but-known-prefix plain-text)))

(defn find-first
  [f li]
  (first (filter f li)))

(defn ecb-block-size
  [encrypt-fn]
  (find-first #(duplicate-blocks? % (encrypt-fn (zero-byte-list (* 2 %)))) (range 2 100)))

(defn find-prefix-size
  [encrypt-fn]
  (let [
    first-duplicate
    (find-first
      #(not-nil? (second %))
      (map
        #(list % (first-duplicate-16-byte-block-index (encrypt-fn (zero-byte-list (+ % 32)))))
        (range 0 15)))
  ]
    (- (* (second first-duplicate) 16) (first first-duplicate))))

(defn find-hidden-plain-text
  [encrypt-fn block-size prefix-size hidden-plain-text]
  (let [
    zero-block (zero-byte-list (- block-size (+ (mod (+ prefix-size (count hidden-plain-text)) block-size) 1)))
    crafty-plain-text (concat zero-block hidden-plain-text)
    bytes-to-compare (+ prefix-size (count crafty-plain-text) 1)
    target-cipher-text (take bytes-to-compare (encrypt-fn zero-block))
    uncovered-byte
      (find-first
        #(=
          target-cipher-text
          (take bytes-to-compare (encrypt-fn (concat crafty-plain-text (list %)))))
        (byte-range))
  ]
    (if (= uncovered-byte (byte 1))
      hidden-plain-text
      (find-hidden-plain-text encrypt-fn block-size prefix-size
        (concat hidden-plain-text (list uncovered-byte))))))

(defn parse-profile
  [s]
  (walk/keywordize-keys
    (apply hash-map
      (string/split s #"(&|=)"))))

(defn profile-for
  [email]
  (str "email=" (string/replace email #"&|=" "") "&uid=10&role=user"))

(defn encrypted-profile-for
  [email]
  (aes-encrypt-byte-list random-but-known-key
    (pad-with-pkcs7 16 (string-to-byte-list (profile-for email)))))

(defn parse-encrypted-profile
  [bl]
  (parse-profile
    (byte-list-to-string
      (remove-pkcs7-padding 16
        (aes-decrypt-byte-list random-but-known-key bl)))))

(defn escape-semi-colon-and-equals
  [s]
  (string/replace (string/replace s #";" "%3B") #"=" "%3D"))

(defn list-split-at
  [position li]
  (seq (split-at position li)))

(defn encrypt-user-data
  [user-data]
  (let [ iv (random-iv) ]
    (concat iv
      (aes-cbc-encrypt random-but-known-key iv
        (pad-with-pkcs7 16
          (string-to-byte-list
            (str
              "comment1=cooking%20MCs;userdata="
              (escape-semi-colon-and-equals user-data)
              ";comment2=%20like%20a%20pound%20of%20bacon")))))))

(defn decrypt-user-data
  [bl]
  (let [
    split-bl (list-split-at 16 bl)
    iv (first split-bl)
    cipher-text (second split-bl)
  ]
    (remove-pkcs7-padding 16
      (aes-cbc-decrypt random-but-known-key iv cipher-text))))

(defn decrypts-to-admin?
  [bl]
  (.contains (byte-list-to-string (decrypt-user-data bl)) ";admin=true;"))

(defn xor-byte-at-position
  [byte-position bl & bytes-to-xor]
  (let [
    split-bl (list-split-at byte-position bl)
    before (first split-bl)
    the-byte (first (second split-bl))
    after (rest (second split-bl))
  ]
    (concat before (list (apply xor-bytes (cons the-byte bytes-to-xor))) after)))

(defn random-plain-text
  []
  (nth
    (map base64-string-to-byte-list (list
      "MDAwMDAwTm93IHRoYXQgdGhlIHBhcnR5IGlzIGp1bXBpbmc="
      "MDAwMDAxV2l0aCB0aGUgYmFzcyBraWNrZWQgaW4gYW5kIHRoZSBWZWdhJ3MgYXJlIHB1bXBpbic="
      "MDAwMDAyUXVpY2sgdG8gdGhlIHBvaW50LCB0byB0aGUgcG9pbnQsIG5vIGZha2luZw=="
      "MDAwMDAzQ29va2luZyBNQydzIGxpa2UgYSBwb3VuZCBvZiBiYWNvbg=="
      "MDAwMDA0QnVybmluZyAnZW0sIGlmIHlvdSBhaW4ndCBxdWljayBhbmQgbmltYmxl"
      "MDAwMDA1SSBnbyBjcmF6eSB3aGVuIEkgaGVhciBhIGN5bWJhbA=="
      "MDAwMDA2QW5kIGEgaGlnaCBoYXQgd2l0aCBhIHNvdXBlZCB1cCB0ZW1wbw=="
      "MDAwMDA3SSdtIG9uIGEgcm9sbCwgaXQncyB0aW1lIHRvIGdvIHNvbG8="
      "MDAwMDA4b2xsaW4nIGluIG15IGZpdmUgcG9pbnQgb2g="
      "MDAwMDA5aXRoIG15IHJhZy10b3AgZG93biBzbyBteSBoYWlyIGNhbiBibG93"))
    (random-int 10)))

(defn aes-cbc-encrypt-plain-text-from
  [plain-text-fn]
  (let [iv (random-iv)]
    (list iv (aes-cbc-encrypt random-but-known-key iv (plain-text-fn)))))

(defn valid-aes-cbc-decrypt?
  [pair]
  (let [
    iv (first pair)
    cipher-text (second pair)
  ]
    (try
      (do
        (aes-cbc-decrypt random-but-known-key iv cipher-text)
        true)
      (catch Exception e false))))

(defn get-block-pairs
  [pair]
  (let [
    iv (first pair)
    cipher-text (second pair)
    blocks (split-byte-list-every-n 16 cipher-text)
    prev-blocks (cons iv (take (- (count blocks) 1) blocks))
  ]
    (map list prev-blocks blocks)))

(defn is-tweak-byte?
  [possible-tweak prev-tweaks block-pair oracle-fn]
  (let [
    prev-block (first block-pair)
    block (second block-pair)
    leading-zeros (zero-byte-list (- 15 (count prev-tweaks)))
    tweaks (cons possible-tweak prev-tweaks)
    padding-byte (byte (count tweaks))
    padding-bytes (repeat (count tweaks) padding-byte)
    tweaks-xor-padding (xor-byte-lists tweaks padding-bytes)
    block-tweak (concat leading-zeros tweaks-xor-padding)
    tweaked-prev-block (xor-byte-lists prev-block block-tweak)
    tweaked-block-pair (list tweaked-prev-block block)
  ]
    (oracle-fn tweaked-block-pair)))

(defn padding-oracle-tweaks
  [prev-tweaks block-pair oracle-fn]
  (let [
    possible-tweaks (filter #(is-tweak-byte? % prev-tweaks block-pair oracle-fn) (byte-range))
  ]
    (if (empty? possible-tweaks)
      nil
      (if (= 15 (count prev-tweaks))
        (cons (first possible-tweaks) prev-tweaks)
        (first (filter not-nil? (map #(padding-oracle-tweaks (cons % prev-tweaks) block-pair oracle-fn) possible-tweaks)))))))


(defn block-padding-oracle-attack
  [block-pair oracle-fn]
  (padding-oracle-tweaks () block-pair oracle-fn))

(defn padding-oracle-attack
  [block-pairs oracle-fn]
  (byte-list-to-string
    (remove-pkcs7-padding 16
      (flatten
        (map #(block-padding-oracle-attack % oracle-fn) block-pairs)))))

(defn counter
  []
  (apply combo/cartesian-product (repeatedly 8 byte-range)))

(defn little-endian-counter
  []
  (map reverse (counter)))

(defn aes-ctr-encrypt
  [key nonce input]
  (xor-byte-lists
    input
    (apply concat
      (map #(aes-encrypt-byte-list key %)
        (map #(concat nonce %) (little-endian-counter))))))

(defn plain-texts-for-shared-ctr-nonce
  []
  (list
    "SSBoYXZlIG1ldCB0aGVtIGF0IGNsb3NlIG9mIGRheQ=="
    "Q29taW5nIHdpdGggdml2aWQgZmFjZXM="
    "RnJvbSBjb3VudGVyIG9yIGRlc2sgYW1vbmcgZ3JleQ=="
    "RWlnaHRlZW50aC1jZW50dXJ5IGhvdXNlcy4="
    "SSBoYXZlIHBhc3NlZCB3aXRoIGEgbm9kIG9mIHRoZSBoZWFk"
    "T3IgcG9saXRlIG1lYW5pbmdsZXNzIHdvcmRzLA=="
    "T3IgaGF2ZSBsaW5nZXJlZCBhd2hpbGUgYW5kIHNhaWQ="
    "UG9saXRlIG1lYW5pbmdsZXNzIHdvcmRzLA=="
    "QW5kIHRob3VnaHQgYmVmb3JlIEkgaGFkIGRvbmU="
    "T2YgYSBtb2NraW5nIHRhbGUgb3IgYSBnaWJl"
    "VG8gcGxlYXNlIGEgY29tcGFuaW9u"
    "QXJvdW5kIHRoZSBmaXJlIGF0IHRoZSBjbHViLA=="
    "QmVpbmcgY2VydGFpbiB0aGF0IHRoZXkgYW5kIEk="
    "QnV0IGxpdmVkIHdoZXJlIG1vdGxleSBpcyB3b3JuOg=="
    "QWxsIGNoYW5nZWQsIGNoYW5nZWQgdXR0ZXJseTo="
    "QSB0ZXJyaWJsZSBiZWF1dHkgaXMgYm9ybi4="
    "VGhhdCB3b21hbidzIGRheXMgd2VyZSBzcGVudA=="
    "SW4gaWdub3JhbnQgZ29vZCB3aWxsLA=="
    "SGVyIG5pZ2h0cyBpbiBhcmd1bWVudA=="
    "VW50aWwgaGVyIHZvaWNlIGdyZXcgc2hyaWxsLg=="
    "V2hhdCB2b2ljZSBtb3JlIHN3ZWV0IHRoYW4gaGVycw=="
    "V2hlbiB5b3VuZyBhbmQgYmVhdXRpZnVsLA=="
    "U2hlIHJvZGUgdG8gaGFycmllcnM/"
    "VGhpcyBtYW4gaGFkIGtlcHQgYSBzY2hvb2w="
    "QW5kIHJvZGUgb3VyIHdpbmdlZCBob3JzZS4="
    "VGhpcyBvdGhlciBoaXMgaGVscGVyIGFuZCBmcmllbmQ="
    "V2FzIGNvbWluZyBpbnRvIGhpcyBmb3JjZTs="
    "SGUgbWlnaHQgaGF2ZSB3b24gZmFtZSBpbiB0aGUgZW5kLA=="
    "U28gc2Vuc2l0aXZlIGhpcyBuYXR1cmUgc2VlbWVkLA=="
    "U28gZGFyaW5nIGFuZCBzd2VldCBoaXMgdGhvdWdodC4="
    "VGhpcyBvdGhlciBtYW4gSSBoYWQgZHJlYW1lZA=="
    "QSBkcnVua2VuLCB2YWluLWdsb3Jpb3VzIGxvdXQu"
    "SGUgaGFkIGRvbmUgbW9zdCBiaXR0ZXIgd3Jvbmc="
    "VG8gc29tZSB3aG8gYXJlIG5lYXIgbXkgaGVhcnQs"
    "WWV0IEkgbnVtYmVyIGhpbSBpbiB0aGUgc29uZzs="
    "SGUsIHRvbywgaGFzIHJlc2lnbmVkIGhpcyBwYXJ0"
    "SW4gdGhlIGNhc3VhbCBjb21lZHk7"
    "SGUsIHRvbywgaGFzIGJlZW4gY2hhbmdlZCBpbiBoaXMgdHVybiw="
    "VHJhbnNmb3JtZWQgdXR0ZXJseTo="
    "QSB0ZXJyaWJsZSBiZWF1dHkgaXMgYm9ybi4="))

(defn cipher-texts-with-shared-ctr-nonce
  [plain-texts]
  (map (partial aes-ctr-encrypt random-but-known-key (zero-byte-list 8))
    (map base64-string-to-byte-list plain-texts)))

(defn cipher-texts-with-shared-ctr-nonce-hard-coded
  []
  (cipher-texts-with-shared-ctr-nonce (plain-texts-for-shared-ctr-nonce)))

(defn cipher-texts-with-shared-ctr-nonce-from-url
  [url]
  (cipher-texts-with-shared-ctr-nonce (get-lines-from-url url)))

(defn longest
  [li]
  (apply max-key count li))

(defn shortest
  [li]
  (apply min-key count li))

(defn score-key-byte
  [key-byte other-bytes]
  (reduce + (map #(byte-score (xor-bytes key-byte %)) other-bytes)))

(defn key-from-plain-text-guess
  [& bytes]
  (let [
    first-byte (first bytes)
    other-bytes (rest bytes)
  ]
    (if (empty? other-bytes)
      (xor-bytes first-byte (byte 32))
      (apply max-key
        #(score-key-byte % other-bytes)
        (map #(xor-bytes first-byte %) (byte-range))))))

(defn guess-shared-key-stream
 [cipher-texts]
 (let [
   longest-cipher-text (longest cipher-texts)
   others (remove #{longest} cipher-texts)
   longest-at-front-cipher-texts (cons longest-cipher-text others)
 ]
   (apply map-longest key-from-plain-text-guess longest-at-front-cipher-texts)))

(defn find-shared-key-stream-multi-byte-xor-style
  [cipher-texts]
  (let [
    shortest-cipher-text-size (count (shortest cipher-texts))
  ]
    (find-multi-byte-xor-key-given-key-size
      (apply concat
        (map #(take shortest-cipher-text-size %) cipher-texts))
      shortest-cipher-text-size)))

(defn decrypt-plain-texts-with-shared-key-stream
  [key-finding-fn cipher-texts]
  (let [
    key-stream (key-finding-fn cipher-texts)
  ]
    (map #(xor-byte-lists key-stream %) cipher-texts)))

(defn add-mod
  [a b modulo]
  (mod (+ a b) modulo))

(defn rotate
  [n li]
  (if (empty? li)
    li
    (let [ shift (mod n (count li)) ]
      (lazy-cat
        (drop shift li)
        (take shift li)))))

(defn shift-right-xor
  [shift n]
  (bit-xor n (bit-shift-right n shift)))

(defn shift-left-magic-xor
  [shift magic n]
  (bit-xor n (bit-and magic (bit-shift-left n shift))))

(defn twister-extract
  [mt]
  (shift-right-xor 18
    (shift-left-magic-xor 15 4022730752
      (shift-left-magic-xor 7 2636928640
        (shift-right-xor 11
          mt)))))

(defn make-mersenne-twister
  ([input]
    (if (instance? Number input)
      (let [
        seed input
        init-seq ((fn twister-init [index mt]
          (lazy-seq (cons mt (twister-init (+ index 1) (bit-and 0xffffffff (+ index (* 1812433253 (bit-xor mt (bit-shift-right mt 30)))))))))
            1 seed)
      ]
        (make-mersenne-twister (take 624 init-seq) true))
      (let [
        init-seq input
      ]
        (make-mersenne-twister init-seq false))))
  ([init-seq run-generate]
  (let [
    state (atom {:index 0 :mt init-seq :gen run-generate})

    extract (fn [current-state]
      (twister-extract (nth (current-state :mt) (current-state :index))))

    increment (fn [current-state]
      (assoc current-state :index (add-mod (current-state :index) 1 624)))

    generate-single (fn [mt mt1 mt397]
      (let [
        y (+ (bit-and mt 0x80000000) (bit-and mt1 0x7fffffff))
        result (bit-xor mt397 (bit-shift-right y 1))
      ]
        (if (odd? y)
          (bit-xor result 2567483615)
	  result)))

    generate-range (fn [from to mt]
      (let [
        mt1 (rotate 1 mt)
        mt397 (rotate 397 mt)
      ]
        (map
          #(if (or (< %1 from) (>= %1 to))
            %2
            (generate-single %2 %3 %4))
          (range) mt mt1 mt397)))

    generate (fn [current-state]
      (if (current-state :gen)
        (assoc current-state :mt
          (generate-range 454 624
            (generate-range 227 454
              (generate-range 0 227 (current-state :mt)))))
        (assoc current-state :gen true)))
  ]
    (fn []
      ((swap!
        state
        #(let [
          generated-state
            (if (zero? (% :index))
              (generate %)
	      %)
	]
          (increment (assoc generated-state :next (extract generated-state)))))
      :next)))))

(defn current-unix-time
  []
  (int (/ (System/currentTimeMillis) 1000)))
 
(defn random-with-time-seed
  [duration]
  (let [
    duration-millis (* duration 1000)
    first-sleep-time (random-int duration-millis)
    second-sleep-time (- duration-millis first-sleep-time)
  ]
    (Thread/sleep first-sleep-time)
    (let [ twister (make-mersenne-twister (current-unix-time)) ]
      (Thread/sleep second-sleep-time)
      (twister))))

(defn find-time-seed
  [duration random-number]
  (let [
    now (int (/ (System/currentTimeMillis) 1000))
  ]
    (find-first
      #(= random-number ((make-mersenne-twister %)))
      (map #(- now %) (range 0 (+ 1 duration))))))

(defn undo-shift-right-xor
  [shift n]
  ((fn undo
    [n and-bits]
    (if (= -1 and-bits)
      n
      (let [
        result (bit-and n and-bits)
	reduced-and-bits (bit-shift-right and-bits shift)
	shifted-result (bit-shift-right result shift)
	remaining-n (bit-xor shifted-result (bit-and-not n and-bits))
      ]
        (+
          result
          (undo remaining-n reduced-and-bits)))))
    n (bit-shift-left (- (math/expt 2 shift) 1) (- 64 shift))))

(defn undo-shift-left-magic-xor
  [shift magic n]
  ((fn undo
    [guess shift-so-far]
    (if (>= shift-so-far 64)
      guess
      (let [
	shift-guess (bit-shift-left guess shift)
	shift-magic-guess (bit-and magic shift-guess)
	shift-magic-guess-xor-n (bit-xor n shift-magic-guess)
	additional-guess-mask (bit-shift-left (- (math/expt 2 shift) 1) shift-so-far)
	additional-guess (bit-and additional-guess-mask shift-magic-guess-xor-n)
      ]
        (undo (+ guess additional-guess) (+ shift-so-far shift)))))
  0 0))

(defn undo-twister-extract
  [random-number]
  (undo-shift-right-xor 11
    (undo-shift-left-magic-xor 7 2636928640
      (undo-shift-left-magic-xor 15 4022730752
        (undo-shift-right-xor 18 random-number)))))

(defn int-list-to-byte-list
  [il]
  (map #(byte (- (mod % 256) 128)) il))

(defn mersenne-encrypt
  [seed input]
  (let [ twister (make-mersenne-twister seed) ]
    (xor-byte-lists
      input
      (int-list-to-byte-list
        (repeatedly (count input) twister)))))

(def random-but-known-seed (random-int 65356))

(defn mersenne-encrypt-unknown-seed-random-prefix
  [input]
  (mersenne-encrypt
    random-but-known-seed
    (concat
      (random-byte-list-random-length 8 40)
      input)))

(defn find-max-prefix
  [trials f]
  (- (apply max (map count (repeatedly trials (partial f (zero-byte-list 1))))) 1))

(defn find-seed
  [f]
  (let [
    max-prefix (find-max-prefix 1000 f)
    match-size 10
    known-text-size (+ max-prefix match-size)
    known-text (zero-byte-list known-text-size)
    cipher-text (f known-text)
    target (take match-size (drop max-prefix cipher-text))
  ]
    (find-first
      #(= target (take match-size (drop max-prefix (mersenne-encrypt % known-text))))
      (range 65356))))

(defn make-password-reset-token-from-seed
  [seed]
  (let [
    token-length 30
    twister (make-mersenne-twister seed)
  ]
    (byte-list-to-hex-string
      (int-list-to-byte-list
        (repeatedly token-length twister)))))
  

(defn create-password-reset-token
  []
  (make-password-reset-token-from-seed (current-unix-time)))

(defn list-contains?
  [value li]
  (not-nil? (some #(= value %) li)))

(defn is-password-token-from-unix-time?
  [tolerance token]
  (let [
    now (current-unix-time)
    positive-range (map #(+ 1 %) (range 0 tolerance))
    negative-range (map #(* -1 %) positive-range)
    full-range (concat '(0) (interleave positive-range negative-range))
    search-range (map #(+ now %) full-range)
  ]
    (list-contains? token (map make-password-reset-token-from-seed search-range))))
  

(defn -main
  [& args]
  ;; work around dangerous default behaviour in Clojure
  (alter-var-root #'*read-eval* (constantly false))

  ; Prints true because the plain text is encrypted then decrypted
  (println "Checking padding on valid encryption. Padding valid?")
  (println (valid-aes-cbc-decrypt? (aes-cbc-encrypt-plain-text-from random-plain-text)))

  ; Prints false because the oracle function finds that the random cipher text doesn't decrypt due to bad padding
  (println "Checking padding when decrypting 'random' cipher text")
  (println (valid-aes-cbc-decrypt? (string-to-byte-list "RANDOM CIPHER TEXT BLOCK PADDED.")))

  (println)

  ; Prints the 10 plain texts recovered using a padding oracle attack
  (doall (map println
    (sort-by #(subs % 0 6)
      (take 10 (distinct
        (map #(padding-oracle-attack % valid-aes-cbc-decrypt?)
          (repeatedly #(get-block-pairs (aes-cbc-encrypt-plain-text-from random-plain-text)))))))))

  (println)

  ; Decrypt the CTR encrypted cipher text
  (println (byte-list-to-string
    (aes-ctr-encrypt
      (string-to-byte-list "YELLOW SUBMARINE")
      (zero-byte-list 8)
      (base64-string-to-byte-list "L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ=="))))
  
  (println)

  ; Automated guessing of shared CTR key stream
  (doall (map println
    (map byte-list-to-string
      (decrypt-plain-texts-with-shared-key-stream
        guess-shared-key-stream
        (cipher-texts-with-shared-ctr-nonce-hard-coded)))))
  
  (println)

  ; Multi byte XOR to recover shared CTR key stream
  (doall (map println
    (map byte-list-to-string
      (decrypt-plain-texts-with-shared-key-stream
        find-shared-key-stream-multi-byte-xor-style
        (cipher-texts-with-shared-ctr-nonce-from-url "https://gist.github.com/tqbf/3336141/raw/d601f0b675feef570188ab2c8f347843f965ee14/gistfile1.txt")))))
  
  (println)

  ; Show that the twister gives the same output when constructed with the same seed
  (println "Twister output (twice)")
  (def twister (make-mersenne-twister 5489))
  (println (twister))

  (def twister (make-mersenne-twister 5489))
  (println (twister))

  (println)

  ; Generate random number using unix time in last 1000 second and recover seed
  (let [
    random-number (random-with-time-seed 1000)
    seed (find-time-seed 1002 random-number)
    check ((make-mersenne-twister seed))
  ]
    (println (list "     random-with-time-seed: " random-number))
    (println (list "            recovered seed: " seed))
    (println (list "check it gives same output: " check)))

  (println)

  ; Recover all the internal state of a Mersenne twister from 624 extractions
  (println "Recover Mersenne twister state and check")
  (def twister (make-mersenne-twister 5489))
  (def twister-output (repeatedly 624 twister))
  (def recovered-twister (make-mersenne-twister (map undo-twister-extract twister-output)))
  (def recovered-twister-output (repeatedly 624 recovered-twister))
  (println (if (= twister-output recovered-twister-output) "MATCH" "NO MATCH"))

  (println)

  ; Check encryption and decryption using Mersenne twister key stream
  (println "Mersenne twister stream encryption and decryption")
  (println (byte-list-to-string (mersenne-encrypt 1234 (mersenne-encrypt 1234 (string-to-byte-list "IN THE TOWN WHERE I WAS BORN")))))

  (println)

  ; Recover seed from Mersenne twister encryption 
  (println "Seed from Mersenne twister encryption")
  (println (find-seed mersenne-encrypt-unknown-seed-random-prefix))

  (println)

  ; Password reset token - create and test
  (println "Password token creation and testing")
  (println (create-password-reset-token))
  (println (is-password-token-from-unix-time? 5 (create-password-reset-token)))
  (println (is-password-token-from-unix-time? 5 "5fa1e265bf1d5d9068c1df36a1aac1c6235298a82c95b10581fd43362d7c"))
)