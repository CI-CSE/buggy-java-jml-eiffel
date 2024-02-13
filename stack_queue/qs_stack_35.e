class
	QS_STACK_35
create
	make
feature {NONE}
	make
		note
			explicit: wrapping, contracts
		require
			is_wrapped: is_wrapped
		do
			unwrap
			top := 0
			exception_is_raised := False
			wrap
		ensure
			check_invariant: inv
			top_is_set: top = 0
			exception_is_raised_is_set: not exception_is_raised
		end

feature
	arr: SIMPLE_ARRAY [INTEGER]
		attribute
			Result := create {SIMPLE_ARRAY [INTEGER]}.make (max)
		end
	exception_is_raised: BOOLEAN
	max: INTEGER = 100

	top: INTEGER

	get_top: INTEGER
		do
			Result := top
		ensure
			result_is_correct: Result = top
		end

	is_empty: BOOLEAN
		do
			Result := get_top < 1
		ensure
			result_is_correct: Result = (top < 1)
			result_is_correct_redundantly: not Result ⇒ 1 <= top
		end

	is_full: BOOLEAN
		require
			is_wrapped: is_wrapped
		do
			Result := top = max
		ensure
			is_wrapped: is_wrapped
			result_is_correct: Result = (top = max)
			result_is_correct_redundantly: not Result ⇒ top < max
		end

	push (x: INTEGER)
		note
			explicit: wrapping
		do
			if not is_full then
				unwrap
				top := top + 1
				arr [top] := x
				wrap
			else
				unwrap
				exception_is_raised := True
				wrap
			end

		ensure
			modify: modify_field (["exception_is_raised", "top", "arr", "closed"], Current)
			size_increased: not old is_full ⇒ size = old size + 1
			if_full: old is_full ⇒ exception_is_raised
			top_in_range: not old is_full ⇒ 1 <= top ∧ top <= max
			element_is_set: not old is_full ⇒ arr.sequence [top] = x
			top_increased: not old is_full ⇒ top = old top + 1
			only_top_changed: not old is_full ⇒ ∀ i: 1 |..| arr.sequence.count ¦ (i /= top ⇒ arr.sequence [i] = (old arr).sequence [i])
			top_in_range_redundantly: 1 <= top ∧ top <= max
		end

	pop: INTEGER
		note
			explicit: wrapping
			status: impure
		require
			is_wrapped: is_wrapped
		do
			if not is_empty then
				Result := arr [top]
				unwrap
				top := top - 1
				wrap
			else
				unwrap
				exception_is_raised := True
				wrap
			end
		ensure
			modify: modify_field (["exception_is_raised", "top", "closed"], Current)
			is_wrapped: is_wrapped
			size_decreased: not (old is_empty) ⇒ size = (old size) - 1
			if_empty: old is_empty ⇒ exception_is_raised
			top_decreased: not (old is_empty) ⇒ top = (old top) - 1
			result_is_old_top: not (old is_empty) ⇒ Result = old arr.sequence [top]
			array_did_not_change: ∀ i: 1 |..| arr.sequence.count ¦ arr.sequence [i] = (old arr.sequence) [i]
		end

	peek: INTEGER
		note
			status: impure
			explicit: wrapping
		require
			is_wrapped: is_wrapped
		do
			if not is_empty then
				Result := arr [top]
			else
				unwrap
				exception_is_raised := True
				wrap
			end
		ensure
			modify: modify_field (["exception_is_raised", "closed"], Current)
			if_empty: is_empty ⇒ exception_is_raised
			if_not_empty: not is_empty ⇒ Result = arr.sequence [top]
			array_did_not_change: ∀ i: 1 |..| arr.sequence.count ¦ arr.sequence [i] = (old arr.sequence) [i] -- MAKE IT WORK
		end

	get_elem (i: INTEGER): INTEGER
		require
			i_in_range: 1 <= i ∧ i <= top
		do
			Result := arr [i]
		ensure
			result_is_correct: Result = arr.sequence [i]
		end

	search (key: INTEGER): INTEGER
		local
			index: INTEGER
		do
			from
				index := top
				Result := -1
			invariant
				index_in_range: -1 <= index ∧ index <= top ∧ Result /= 0
				not_found_until_now: Result = -1 ⇒ ∀ i: (index + 1) |..| top ¦ arr.sequence [i] /= key
				if_found: (0 < Result ∧ Result <= top) ⇒ arr.sequence [Result] = key
			until
				index < 1 ∨ Result /= -1
			loop
				if get_elem (index) = key then
					Result := index
				else
					index := index - 1
				end
			variant
				index - if Result = -1 then 0 else 1 end
			end
		ensure
			result_not_zero: Result /= 0
			if_found: (1 <= Result ∧ Result <= top) ⇒ arr.sequence [Result] = key
			not_found: Result = -1 ⇒ ∀ i: 1 |..| top ¦ arr.sequence [i] /= key
		end

	is_contain (key: INTEGER): BOOLEAN
		local
			index: INTEGER
		do
			from
				index := top
				Result := False
			invariant
				index_in_range: 0 <= index ∧ index <= top
				not_found_until_now: not Result ⇒ ∀ i: (index + 1) |..| top ¦ arr.sequence [i] /= key
				found: Result ⇒ ∃ i: 1 |..| top ¦ arr.sequence [i] = key
			until
				index < 1 ∨ Result
			loop
				if key = get_elem (index) then
					Result := True
				else
					index := index - 1
				end
			variant
				index - if Result then 1 else 0 end
			end
		ensure
			not_found: not Result ⇒ ∀ i: 1 |..| top ¦ arr.sequence [i] /= key
			found: Result ⇒ ∃ i: 1 |..| top ¦ arr.sequence [i] = key
		end

	size: INTEGER
		do
			Result := get_top
		ensure
			result_is_correct: Result = top
		end

invariant
	owns_the_array: owns = (create {MML_SET [ANY]}.singleton (arr))
	top_in_range: 0 <= top ∧ top <= max
	arr_length_is_max: arr.sequence.count = max

end
