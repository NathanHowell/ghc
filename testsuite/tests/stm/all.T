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
