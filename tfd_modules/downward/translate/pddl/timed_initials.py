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
			self.symbol = self.fact[1][0]
			self.args = self.fact[1][1:]
		elif self.fact[0] == '=':
			if f_expression.isFloat(self.fact[2]):
				self.type = 'NUMERICAL_FUNCTION'
				self.value = float(self.fact[2])
				self.symbol = self.fact[1][0]
				self.args = self.fact[1][1:]
			else:
				self.type = 'OBJECT_FUNCTION'
				self.value = self.fact[2]
				self.symbol = self.fact[1][0]
				self.args = self.fact[1][1:]
		else:
			self.type = 'BOOLEAN'
			self.value = True
			self.symbol = self.fact[0]
			self.args = self.fact[1:]

	def create_initial_value(self, init_):
		if self.type in {'BOOLEAN', 'NEGATED_BOOLEAN'}:
			for other_fact in init_:
				if type(other_fact) is conditions.Atom:
					if self.symbol == other_fact.predicate and self.args == other_fact.args:
						fact = [self.symbol]+self.args
						return TimedInitial(0.0, fact)
			fact = ['not', [self.symbol]+self.args]
			return TimedInitial(0.0, fact)
		if self.type is 'NUMERICAL_FUNCTION':
			for other_fact in init_:
				if type(other_fact) is f_expression.Assign:
					if other_fact.fluent:
						fact = copy.deepcopy(self.fact)
						fact[2] = other_fact.expression
						return TimedInitial(0.0, fact)
		if self.type is 'OBJECT_FUNCTION':
			for other_fact in init_:
				if type(other_fact) is conditions.Atom:
					if '{}!val'.format(self.symbol) == other_fact.predicate:
						print other_fact.predicate
						print other_fact.args
						print self.args
						if all(a==b.name for a, b in itertools.izip(self.args, other_fact.args[:-1])):
							fact = copy.deepcopy(self.fact)
							fact[2] = other_fact.args[-1].name
							print fact
							return TimedInitial(0.0, fact)

	def __str__(self):
			return "%s (at %s %s)" % (self.__class__.__name__, self.time, self.fact)

	def dump(self, indent="	"):
			print "%s%s (at %s %s)" % (indent, self.__class__.__name__, self.time, self.fact)
		
	def to_effect(self):
		if self.type is 'BOOLEAN':
			return '({})'.format(' '.join([self.symbol] + self.args))
		if self.type is 'NEGATED_BOOLEAN':
			return '(not ({}))'.format(' '.join([self.symbol] + self.args))
		if self.type is 'NUMERICAL_FUNCTION':
			return '(assign ({}) {})'.format(' '.join([self.symbol] + self.args), self.value)
		if self.type is 'OBJECT_FUNCTION':
			return '(assign ({}) {})'.format(' '.join([self.symbol] + self.args), self.value)

def pairwise(iterable):
		"s -> (s0,s1), (s1,s2), (s2, s3), ..."
		a, b = itertools.tee(iterable)
		next(b, None)
		return itertools.izip(a, b)

def protect_timed_predicates(predicates_, actions_, init_, goal_, timed_initials_):
	# find all predicates and fuctions and build value timeline
	predicate_values = {} # {predicate: [ti1=TimedInitial(), ti2, ...]}
	for ti in timed_initials_:
		key = ' '.join([ti.symbol] + ti.args) # regular fact
		if key not in predicate_values:
			predicate_values[key] = [ti.create_initial_value(init_)]
		predicate_values[key].append(ti)
	
	action_template = '''
  (:durative-action {name}protected
    :parameters ()
    :duration (= ?duration {duration})
    :condition (and 
      (over all {previous_value})
    )
    :effect (and
      (at end {next_value})
      (at end ({protected_predicate}))
    )
  )'''
	# add protection_actions with over all conditions
	counter = itertools.count()
	goal_list = []
	ti_actions = []
	for key, tis in predicate_values.viewitems():
		for ti0, ti1 in pairwise(tis): # [ti1=TimedInitial(), ti2, ...]
			name = 'timed_initial_{}__'.format(next(counter))
			# add predicates
			protected_predicate = predicates.Predicate(name+'protected', [])
			predicates_.append(protected_predicate)
			# add goal
			goal_list.append(conditions.Atom(protected_predicate.name, []))
			duration = ti1.time - ti0.time
			previous_value = fact_string_from_nested_list(ti0.fact)
			next_value = fact_string_from_nested_list(ti1.fact)
			action_string = action_template.format(name=name, duration=duration, 
				previous_value=previous_value, next_value=next_value, protected_predicate=protected_predicate.name)
			print(action_string)
	return goal_list, ti_actions

def schedule_timed_initials(predicates_, actions_, init_, goal_, timed_initials_):
	# add init
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
		scheduled_predicate = predicates.Predicate(name+'scheduled', [])
		predicates_.append(scheduled_predicate)
		# add goal
		goal_list.append(conditions.Atom(scheduled_predicate.name, []))
		# add action
		#fact_string =	effect_string_from_initial(ti.fact)
		#fact_string =	effect_list_from_conjunction(ti.fact)
		facts = []
		for ti in tis:
			facts.append('      (at end {})'.format(ti.to_effect()))
		action_string = '''
  (:durative-action {name}scheduled
    :parameters ()
    :duration (= ?duration {time})
    :condition (at start (initial_state))
    :effect (and{disable_initial_state}
      (at end ({predicate}))
{facts}
    )
  )'''.format(name=name, time=ti.time, predicate=scheduled_predicate.name,
			disable_initial_state=disable_initial_state, facts='\n'.join(facts))
		print(action_string)
		action = actions.DurativeAction.parse(parser.parse_nested_list([action_string]))
		ti_actions.append(action)
		disable_initial_state = ''
	return goal_list, ti_actions

def compile_away(predicates_, actions_, init_, goal_, timed_initials_):
	initial_state_predicate = predicates.Predicate('initial_state', [])
	predicates_.append(initial_state_predicate)
	
	protect_goals, protect_actions = protect_timed_predicates(predicates_, actions_, init_, goal_, timed_initials_)
	schedule_goals = []
	schedule_actions = []
	#schedule_goals, schedule_actions = schedule_timed_initials(predicates_, actions_, init_, goal_, timed_initials_)
	
	
	# add goals
	goal_.parts += tuple(protect_goals + schedule_goals)
	#goal_.dump()
	# add negated precontition to all other actions
	[at_start, overall, at_end] = conditions.parse_durative_condition(parser.parse_nested_list(['(at start (not (initial_state)))']))
	for da in actions_:
		da.condition[0].parts += (at_start, )
	actions_.extend(protect_actions)
	actions_.extend(schedule_actions)
	
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
	