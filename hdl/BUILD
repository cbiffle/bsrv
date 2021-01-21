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

bluespec_library('Tangy5', sources = ['Tangy5.bsv'])

bluespec_sim('Tangy5Tb',
    top = 'Tangy5Tb.bsv',
    modules = ['mkTb'],
    deps = [
        ':Tangy5',
    ],
)

bluesim_binary('Tangy5Tb-bin',
    env = 'bluesim_default',
    top = ':Tangy5Tb#mkTb',
    deps = [':Tangy5Tb'],
)
