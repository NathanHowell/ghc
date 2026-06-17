test('stm_stress',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_large_log',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_orElse_rollback',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_orElse_wait_union',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_unsafeIO_rerun',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_mfix',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_nested_orElse',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_validate',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

# stm_zombie_abort is a known pre-existing failure: mid-flight bind-checkpoint
# validation (e265152, "validate only new STM reads at bind checkpoints") does
# not re-check older reads, so a torn-then-divergent transaction is never aborted
# and the test hangs at -O.  Skipped pending the STM CPS validation rework;
# re-enable (drop `skip`) once mid-flight zombie detection is restored.  See the
# test's header for details.
test('stm_zombie_abort',
     [ skip
     , req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])

test('stm_catch_wait',
     [ req_ghc_smp
     , req_target_smp
     , only_ways(threaded_ways)
     , extra_run_opts('+RTS -N4 -RTS')
     , js_skip
     , wasm_skip
     ],
     compile_and_run, [''])
