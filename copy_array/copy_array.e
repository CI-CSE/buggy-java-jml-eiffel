class
	COPY_ARRAY

feature
	copy_array (a_arr_1, a_arr_2: SIMPLE_ARRAY [INTEGER]; a_begin, a_end: INTEGER)
		note
			explicit: wrapping, contracts
		require
			a_arr_1.is_wrapped -- semantic collaboration
			a_arr_2.is_wrapped -- semantic collaboration
			arrays_non_empty: a_arr_1.sequence.count > 0 and a_arr_2.sequence.count > 0
			indeces_lower_bounds: 1 <= a_begin  and 1 <= a_end and a_begin <= a_end
			indeces_upper_bounds: a_begin <= a_arr_1.sequence.count and a_begin <= a_arr_2.sequence.count and a_end <= (a_arr_1.sequence.count + 1) and a_end <= (a_arr_2.sequence.count + 1)
		local
			l_k: INTEGER
		do
			from
				l_k := a_begin
			invariant
				source_array_wrapped: a_arr_1.is_wrapped -- semantic collaboration
				target_array_wrapped: a_arr_2.is_wrapped -- semantic collaboration
				terminal_index_constant: a_end = a_end.old_ -- semantic collaboration
				target_array_lenght_constant: a_arr_2.sequence.count = a_arr_2.sequence.count.old_ -- semantic collaboration
				local_within_bounds: a_begin <= l_k and l_k <= a_end
				partially_copied: ∀ i: a_begin |..| (l_k - 1) ¦ a_arr_2.sequence [i] = a_arr_1.sequence [i]
			until
				a_end - l_k <= 0
			loop
				a_arr_2 [l_k] := a_arr_1 [l_k]
				l_k := l_k + 1
			variant
				(a_end - l_k)
			end
		ensure
			target_array_copy_of_initial_array_from_initial_index_to_terminal_index: ∀ i: a_begin |..| (a_end - 1) ¦ a_arr_2.sequence [i] = a_arr_1.sequence [i]
			modify (a_arr_2)
		end
end
