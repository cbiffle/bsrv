# vim:syntax=python:

bluespec_library('Common', sources = ['Common.bsv'])

# Repeating pattern of targets for each basic core design:
def basic_core(name):
    bluespec_library(name,
        sources = [name + '.bsv'],
        deps = [':Common'],
    )

    bluespec_sim(name + 'Tb',
        top = name + 'Tb.bsv',
        modules = ['mkTb'],
        deps = [
            ':Common',
            ':' + name,
        ],
    )

    bluesim_binary(name + 'Tb-bin',
        env = 'bluesim_default',
        top = ':' + name + 'Tb#mkTb',
        deps = [':' + name + 'Tb'],
    )

basic_core('Corny5')
basic_core('Dinky5')
basic_core('Tangy5')
