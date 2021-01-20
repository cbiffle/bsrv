# vim:syntax=python:

bluespec_library('Dinky5', sources = ['Dinky5.bsv'])

bluespec_sim('Dinky5Tb',
    top = 'Dinky5Tb.bsv',
    modules = ['mkTb'],
    deps = [
        ':Dinky5',
    ],
)

bluesim_binary('Dinky5Tb-bin',
    env = 'bluesim_default',
    top = ':Dinky5Tb#mkTb',
    deps = [':Dinky5Tb'],
)
