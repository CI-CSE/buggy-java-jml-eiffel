note
	model: key, arr

class
	FIND_IN_ARRAY_2

create
	make, make_key

feature {NONE}

	make (input_arr: SIMPLE_ARRAY [INTEGER])
		note
			explicit: wrapping, contracts
			status: creator
		require
			input_arr_wrapped: input_arr.is_wrapped
		local
			l_size: INTEGER
		do
			l_size := input_arr.count
			create arr.make (l_size)
			create arr.make_from_array (input_arr)

			key := 0
		ensure
			arr_equal: ∀ i: 1 |..| input_arr.count ¦ input_arr.sequence [i] = arr.sequence [i]
			key_zero: key = 0
		end

	make_key (input_arr: SIMPLE_ARRAY [INTEGER]; a_key: INTEGER)
		note
			status: creator
			explicit: wrapping, contracts
		require
			input_arr_wrapped: input_arr.is_wrapped
		local
			l_size: INTEGER
		do
			l_size := input_arr.count
			create arr.make (l_size)
			create arr.make_from_array (input_arr)

			set_key (a_key)
		ensure
			key_set: key = a_key
			arr_equal: ∀ i: 1 |..| input_arr.count ¦ input_arr.sequence [i] = arr.sequence [i]
		end

	set_key (a_key: INTEGER)
		require
			no_observers: observers.is_empty
		do
			key := a_key
		ensure
			modify_model ("key", Current)
			key_set: key = a_key
		end

feature

	key: INTEGER

	arr: SIMPLE_ARRAY [INTEGER]

	get_key: INTEGER
		do
			Result := if key = 0 then 1 else 0 end -- Result := key
		ensure
			result_is_key: Result = key
		end

	get_arr (i: INTEGER): INTEGER
		require
			i_in_bounds: 1 <= i and i <= arr.count
		do
			Result := arr [i]
		ensure
			result_is_ith_element: Result = arr.sequence [i]
		end

	size: INTEGER
		do
			Result := arr.count
		ensure
			result_is_count: Result = arr.count
		end

	find_last: INTEGER
		local
			index: INTEGER
		do
			from
				index := size
			invariant
				result_bounds: 0 <= Result and Result <= arr.count
				result_and_index: Result /= 0 ⇒ Result = index + 1

				index_bounds: 0 <= index and index <= arr.count
				no_after: Result = 0 ⇒ ∀ i: (index + 1) |..| arr.count ¦ arr.sequence [i] /= key
				found: Result /= 0 ⇒ arr.sequence [index + 1] = key
					and ∀ i: (index + 2) |..| arr.count ¦ arr.sequence [i] /= key
			until
				Result /= 0 or 1 > index
			loop
				if get_arr (index) = get_key then
					Result := index
				end
				index := index - 1
			variant
				index
			end
		ensure
			index_is_last: 1 <= Result and Result <= arr.count ⇒ arr.sequence [Result] = key
				and ∀ i: (Result + 1) |..| arr.count ¦ arr.sequence [i] /= key

			zero_is_not_present: Result = 0 ⇒ ∀ i: 1 |..| arr.count ¦ arr.sequence [i] /= key
		end

	find_first: INTEGER
		local
			index: INTEGER
		do
			from
				index := 1
			invariant
				result_bounds: 0 <= Result and Result <= arr.count
				restul_and_index: Result /= 0 ⇒ Result = index - 1

				index_bounds: 1 <= index and index <= arr.count + 1
				no_before: Result = 0 ⇒ ∀ i: 1 |..| (index - 1) ¦ arr.sequence [i] /= key
				found: Result /= 0 ⇒ arr.sequence [index - 1] = key
					and ∀ i: 1 |..| (index - 2) ¦ arr.sequence [i] /= key
			until
				Result /= 0 or index > size
			loop
				if get_arr (index) = get_key then
					Result := index
				end

				index := index + 1
			variant
				size - index
			end
		ensure
			index_is_first: 1 <= Result and Result <= arr.count ⇒ arr.sequence [Result] = key
				and ∀ i: 1 |..| (Result - 1) ¦ arr.sequence [i] /= key
			zero_is_not_present: Result = 0 ⇒ ∀ i: 1 |..| arr.count ¦ arr.sequence [i] /= key
		end

	is_more_than_one_key: BOOLEAN
		local
			first, last: INTEGER
		do
			first := find_first
			last := find_last
			Result := first /= last
		ensure
			result_def: result = (find_last /= find_first)
		end

invariant
	owns_def: owns = create {MML_SET [ANY]}.singleton (arr)

end
