module

/-!
# A concurrent Bloom filter (first attempt)

Ported from clutch/theories/coneris/examples/bloom_filter/concurrent_bloom_filter.v

## Omitted
The whole content of the Rocq file (everything after the `Require`s and `Set Default Proof
Using`) is inside one comment `(* ... *)`: the section `conc_bloom_filter` with the programs
`init_bloom_filter`, `insert_bloom_filter`, `lookup_bloom_filter`, the admitted lemmas
`hash_token_non_empty`, `hash_token_combine`, `hash_frag_valid`, `con_hash_inv_list_cons`, the
definitions `con_hash_inv_list`, `bloom_filter_inv`, and the unfinished (`Admitted`) specs
`bloom_filter_init_spec`, `bloom_filter_insert_thread_spec`. None of it is live Rocq code, so
nothing is ported. The live concurrent Bloom filter is
`Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt` (from `concurrent_bloom_filter_alt.v`).

This module only exists to record the (empty) port and its namespace.
-/

@[expose] public section

namespace Coneris.Examples.BloomFilter.ConcurrentBloomFilter

end Coneris.Examples.BloomFilter.ConcurrentBloomFilter
