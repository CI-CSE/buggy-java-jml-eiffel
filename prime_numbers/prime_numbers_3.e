note
	model: prime_array
class

	PRIME_NUMBERS_3
create
	make
feature {NONE}
	make (a_n: INTEGER)
		require
			obs: observers.is_empty
			wrapped: is_wrapped
			a_n_nonneg: a_n >= 0
		do
			create prime_array.make (a_n)
		ensure
			default_initialization: prime_array.sequence.count = a_n
		end

	div (a_n, a_d: INTEGER): BOOLEAN
		require
			a_n_lower_bound: 2 <= a_n
			a_d_lower_bound: 2 <= a_d
		do
			Result := (a_n \\ a_d) = 0
		ensure
			a_n_is_multiple_a_d: (Result) = (a_n \\ a_d = 0)
		end

	prime_array: SIMPLE_ARRAY [INTEGER]

feature
	prime_list (a_n: INTEGER): SIMPLE_ARRAY [INTEGER]
		note
			status: impure
			explicit: wrapping
		require
			obs: observers.is_empty
			wrapped: is_wrapped
			a_n_within_bounds: 1 <= a_n 
		local
			l_count_count, l_status, l_num, l_count, l_j: INTEGER
		do
			l_status := 1
			l_num := 3
			unwrap
			prime_array := create {SIMPLE_ARRAY [INTEGER]}.make (a_n)
			prime_array [1] := 2

			from
				l_count := 2
				l_count_count := l_count
			invariant
				modify (prime_array)
				prime_array_wrapped: prime_array.is_wrapped
				prime_array_constant_lenght: prime_array.sequence.count = a_n
				l_status_eq_one: l_status = 1
				l_num_maximal: ∀ i: 1 |..| (l_count - 1) ¦ prime_array.sequence [i] < l_num
				count_within_bounds: 2 <= l_count and l_count <= a_n + 1 and 3 <= l_num
				is_new: ∀ k: 1 |..| (l_count - 1) ¦ l_num /= prime_array.sequence [k]
				partial_prime_implies_coprime_with_all_smaller: ∀ i: 1 |..| (l_count - 1) ¦ ∀ j: 2 |..| (prime_array.sequence [i] // 2) ¦ not (prime_array.sequence [i] \\ j = 0)
				is_partially_sorted: ∀ i: 1 |..| (l_count - 1) ¦ ∀ j: 1 |..| (i - 1) ¦ prime_array.sequence [j] < prime_array.sequence [i]
			until
				l_count > (a_n + 1) -- l_count > a_n
			loop
				l_count_count := l_count
				from
					l_j := 2
				invariant
					modify (prime_array)
					prime_array.is_wrapped
					prime_array_constant_lenght: prime_array.sequence.count = a_n
					l_status_eq_zero_impl_l_num_has_divisor: l_status /= 0 implies ∀ i: 2 |..| (l_j - 1) ¦ l_num \\ i /= 0
					is_l_j_within_bounds: 2 <= l_j and l_j <= (l_num // 2) + 1
					is_count_within_bounds: 2 <= l_count and l_count <= a_n + 1 and 3 <= l_num
					is_new: ∀ k: 1 |..| (l_count - 1) ¦ l_num /= prime_array.sequence [k]
					l_num_maximal_prime_array: ∀ i: 1 |..| (l_count - 1) ¦ prime_array.sequence [i] < l_num
					is_partially_sorted: ∀ i: 1 |..| (l_count - 1) ¦ ∀ j: 1 |..| (i - 1) ¦ prime_array.sequence [j] < prime_array.sequence [i]
					partial_partial_prime_implies_coprime_with_all_smaller: ∀ i: 1 |..| (l_count - 1) ¦ ∀ j: 2 |..| (prime_array.sequence [i] // 2) ¦ not (prime_array.sequence [i] \\ j = 0)
				until
					(l_j > l_num // 2) or (l_num \\ l_j = 0)
				loop
					l_j := l_j + 1
				variant
					l_num - l_j
				end
			if l_num \\ l_j = 0 then
				l_status := 0
			end
			if  l_status /= 0 then
				prime_array [l_count] := l_num
				l_count := l_count + 1
			end
			l_status := 1
			l_num := l_num + 1
			variant
				{INTEGER}.Max_value - l_num
			end
			Result := prime_array
			wrap
		ensure
			modify (prime_array)
			modify_model ("prime_array", Current)
			wrapped: is_wrapped
			is_attached: attached Result
			prime_implies_coprime_with_all_smaller: ∀ i: 1 |..| prime_array.sequence.count ¦ ∀ j: 2 |..| (prime_array.sequence [i] // 2) ¦ not (prime_array.sequence [i] \\ j = 0)
			all_primes_are_different: ∀ i: 1 |..| prime_array.sequence.count ¦ ∀ j: 1 |..| prime_array.sequence.count ¦ (i /= j) implies (prime_array.sequence [i] /= prime_array.sequence [j])
			prime_array_constant_lenght: prime_array.sequence.count = a_n
		end

invariant
	ownership: owns = (create {MML_SET [ANY]}.singleton (prime_array))
end
