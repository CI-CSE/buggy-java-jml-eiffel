note
	model: fib
class
	FIBONACCI_TRANSLATION_4
inherit
	ANY
redefine default_create end

create
	default_create, make

feature
	fib: detachable SIMPLE_ARRAY [INTEGER]
		note
			option: stable
		attribute
		end

	default_create
		note
			status: creator
			explicit: wrapping, contracts
		do
			create fib.make (2)
			fib [1] := 0
			fib [2] := 1
		ensure then
			fib_attached: attached fib
			first_fib_is_zero_second_fib_is_one: fib.sequence [1] = 0 and fib.sequence [2] = 1
		end

	make (a_size: INTEGER)
		note
			status: creator
			explicit: wrapping, contracts
		do
			if 2 <= a_size and a_size > 93 then -- if 2 <= a_size and a_size <= 93 then
				create fib.make (a_size)
				fib [1] := 0
				fib [2] := 1
			else
				check fib_not_attached: not attached fib end
			end
		ensure
			normal_behaviour: (attached fib) implies ((2 <= a_size and a_size <= 93) and ((fib.sequence [1] = 0 and fib.sequence [2] = 1) and (∀ i: 3 |..| (fib.sequence.count - 1) ¦ fib.sequence [i] = 0))) 
			exeptional_behaviour: (not attached fib) implies ((a_size < 2) or (93 < a_size)) 
		end

	get_fib (a_index: INTEGER): INTEGER
		note
			explicit: wrapping, contracts
		require
			fib_attached: attached fib -- added
			fib.is_wrapped -- added
			a_index_within_bounds: 1 <= a_index and a_index <= fib.sequence.count
		do
			if attached fib then
				Result := fib [a_index]
			end
		ensure
			fib_attached: attached fib
			result_is_fibonacci_in_sequence: Result = fib [a_index]
		end

	fib_compute
		note
			explicit: wrapping, contracts
		require
			fib_attached: attached fib
			fib.is_wrapped -- added
			first_fib_is_zero_second_fib_is_one: fib.sequence [1] = 0 and fib.sequence [2] = 1
		local
			l_index: INTEGER
			l_sequence_count: INTEGER
		do
			if attached fib then l_sequence_count := fib.sequence.count end
			from
				l_index := 3
			invariant
				fib_attached: attached fib -- added
				fib.is_wrapped -- added
				l_sequence_count = fib.sequence.count -- added
				l_index_within_bounds: 3 <= l_index and l_index <= (fib.sequence.count + 1)
				partial_definition_fibonacci: ∀ i: 3 |..| (l_index - 1) ¦ fib.sequence [i] = fib.sequence [i - 1] + fib.sequence [i - 2]
				sequence_is_partially_sorted: ∀ i: 3 |..| (l_index - 1) ¦ ∀ j: 3 |..| (i - 1) ¦ fib.sequence [j] < fib.sequence [i]
			until
				(attached fib) implies (l_index > fib.sequence.count)
			loop
				check assume: attached fib implies fib.sequence [l_index - 2] + fib.sequence [l_index - 1] > 0 end
				if attached fib then
					fib [l_index] := fib [l_index - 2] + fib [l_index - 1]
					l_index := l_index + 1
				end
				check assume: attached fib implies fib.sequence [l_index - 2] < fib.sequence [l_index - 1] end
			variant
				l_sequence_count - l_index + 1
			end
		ensure
			fib_attached: attached fib
			modify (fib)
			definition_fibonacci: ∀ i: 3 |..| fib.sequence.count ¦ fib.sequence [i] = fib.sequence [i - 1] + fib.sequence [i - 2]
			sequence_is_sorted: ∀ i: 3 |..| fib.sequence.count ¦ ∀ j: 3 |..| (i - 1) ¦ fib.sequence [j] < fib.sequence [i]
		end


invariant
	ownership: owns = if attached fib then
	(create {MML_SET [ANY]}.singleton (fib)) else
	(create {MML_SET [ANY]}) end
	bounds_fib_sequence: (attached fib) implies (2 <= fib.count and fib.count <= 93) 
end

