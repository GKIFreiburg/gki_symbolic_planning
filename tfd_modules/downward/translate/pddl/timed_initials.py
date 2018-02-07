import sys

import pddl_types
import functions
import parser
import actions
import predicates
import conditions
import f_expression
import effects
import itertools
import copy

class TimedInitial(object):
	TYPES = {'BOOLEAN', 'NEGATED_BOOLEAN', 'NUMERICAL_FUNCTION', 'OBJECT_FUNCTION'}
	
	def __init__(self, time, init_fact):
		self.time = time
		self.fact = init_fact # nested list
		if self.fact[0] == 'not':
			self.type = 'NEGATED_BOOLEAN'
			self.value = False
			self.predicate = tuple(self.fact[1])
			self.atom = conditions.Atom(self.fact[1][0], [conditions.parse_term(term) for term in self.fact[1][1:]])
		elif self.fact[0] == '=':
			if f_expression.isFloat(self.fact[2]):
				self.type = 'NUMERICAL_FUNCTION'
				self.value = float(self.fact[2])
				self.predicate = tuple(self.fact[1])
				self.atom = f_expression.parse_assignment(fact)
			else:
				self.type = 'OBJECT_FUNCTION'
				self.value = self.fact[2]
				self.predicate = tuple(self.fact[1])
				function = conditions.parse_term(self.fact[1])
				terms = function.args
				terms.append(conditions.parse_term(self.fact[2]))
				atomname = conditions.function_predicate_name(function.name)
				self.atom = conditions.Atom(atomname, terms)
		else:
			self.type = 'BOOLEAN'
			self.value = True
			self.atom = conditions.Atom(self.fact[0], [conditions.parse_term(term) for term in self.fact[1:]])
			self.predicate = tuple(self.fact)

	def create_initial_value(self, init_):
		if self.type in {'BOOLEAN', 'NEGATED_BOOLEAN'}:
			for other_fact in init_:
				if self.atom == other_fact:
					return TimedInitial(0.0, list(self.predicate))
			return TimedInitial(0.0, ['not', list(self.predicate)])
		if self.type is 'NUMERICAL_FUNCTION':
			for other_fact in init_:
				if type(other_fact) is f_expression.Assign:
					if other_fact.fluent == self.atom.fluent:
						fact = copy.deepcopy(self.fact)
						fact[2] = other_fact.expression.value
						return TimedInitial(0.0, fact)
		if self.type is 'OBJECT_FUNCTION':
			for other_fact in init_:
				if type(other_fact) is conditions.Atom:
					if self.atom.predicate == other_fact.predicate:
						if all(a==b for a, b in itertools.izip(self.atom.args[:-1], other_fact.args[:-1])):
							fact = copy.deepcopy(self.fact)
							fact[2] = other_fact.args[-1].name
							return TimedInitial(0.0, fact)

	def __str__(self):
			return "%s (at %s %s)" % (self.__class__.__name__, self.time, self.fact)

	def dump(self, indent="	"):
			print "%s%s (at %s %s)" % (indent, self.__class__.__name__, self.time, self.fact)
		
	def to_effect(self):
		if self.type is 'BOOLEAN':
			return '({})'.format(' '.join(self.predicate))
		if self.type is 'NEGATED_BOOLEAN':
			return '(not ({}))'.format(' '.join(self.predicate))
		if self.type is 'NUMERICAL_FUNCTION':
			return '(assign ({}) {})'.format(' '.join(self.predicate), self.value)
		if self.type is 'OBJECT_FUNCTION':
			return '(assign ({}) {})'.format(' '.join(self.predicate), self.value)

def schedule_timed_initials(predicates_, actions_, init_, goal_, timed_initials_):
	# find all predicates and fuctions and build value timeline
	predicate_values = {} # {predicate: [ti1=TimedInitial(), ti2, ...]}
	for ti in timed_initials_:
		if ti.predicate not in predicate_values:
			predicate_values[ti.predicate] = [ti.create_initial_value(init_)]
		predicate_values[ti.predicate].append(ti)

	# add init
	initial_state_predicate = predicates.Predicate('initial_state', [])
	predicates_.append(initial_state_predicate)

	init_.append(conditions.Atom('initial_state', []))
	disable_initial_state = '\n      (at start (not (initial_state)))'
	
	# merge timed initials occuring at the same time into one conjuction
	merged_initials = {} # {time: [ti1=TimedInitial, ti2, ...]}
	for ti in timed_initials_:
		if not ti.time in merged_initials:
			merged_initials[ti.time] = [ti]
		else:
			merged_initials[ti.time].append(ti)
	
	goal_list = []
	ti_actions = []
	counter = itertools.count()
	for tis in sorted(merged_initials.values(), key=lambda tis: tis[0].time):
		name = 'timed_initial_{}__'.format(next(counter))
		# add predicates
		scheduled_predicate = predicates.Predicate(name+'-scheduled', [])
		predicates_.append(scheduled_predicate)
		# add goal
		goal_list.append(conditions.Atom(scheduled_predicate.name, []))

		# add action
		facts = []
		previous_facts = []
		for ti in tis:
			facts.append('      (at end {})'.format(ti.to_effect()))
			value_timeline = predicate_values[ti.predicate]
			#print map(str, value_timeline)
			previous_value = max((ti2 for ti2 in value_timeline if ti2.time < ti.time), key=lambda ti2: ti2.time)
			#print previous_value.time, previous_value.to_effect()
			previous_facts.append('      (at end {})'.format(previous_value.to_effect()))
		action_string = '''
  (:durative-action {name}scheduled
    :parameters ()
    :duration (= ?duration {time})
    :condition (and
      (at start (initial_state))
{previous_facts}
    )
    :effect (and{disable_initial_state}
      (at end ({predicate}))
{facts}
    )
  )'''.format(name=name, time=ti.time, predicate=scheduled_predicate.name,
			disable_initial_state=disable_initial_state, facts='\n'.join(facts), previous_facts='\n'.join(previous_facts))
		print(action_string)
		#assert 0
		action = actions.DurativeAction.parse(parser.parse_nested_list([action_string]))
		ti_actions.append(action)
		disable_initial_state = ''
	# add goals
	goal_.parts += tuple(goal_list)
	#goal_.dump()
	# add negated precontition to all other actions
	[at_start, overall, at_end] = conditions.parse_durative_condition(parser.parse_nested_list(['(at start (not (initial_state)))']))
	for da in actions_:
		da.condition[0].parts += (at_start, )
	actions_.extend(ti_actions)

def compile_away(predicates_, actions_, init_, goal_, timed_initials_):
	
	#protect_timed_predicates(predicates_, actions_, init_, goal_, timed_initials_)
	schedule_timed_initials(predicates_, actions_, init_, goal_, timed_initials_)
	
def effect_list_from_conjunction(fact_list):
	facts = []
	fact_template = '(at end {})'
	if type(fact_list) == list and len(fact_list) > 1 and fact_list[0] == 'and':
		for item in fact_list[1:]:
			facts.append('(at end {})'.format(fact_string_from_nested_list(item)))
	else:
		facts.append('(at end {})'.format(fact_string_from_nested_list(fact_list)))
	return '\n				'.join(facts)
	
def fact_string_from_nested_list(fact):
	parts = []
	for item in fact:
		if type(item) == list:
			parts.append(fact_string_from_nested_list(item))
		else:
			parts.append(item)
	return '({})'.format(' '.join(parts))
	