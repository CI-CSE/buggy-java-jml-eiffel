note
	model: location

class
	LINEAR_SEARCH

feature

	location: INTEGER

	linear_search (search: INTEGER; array: SIMPLE_ARRAY [INTEGER]): INTEGER
		note
			status: impure
			explicit: contracts
		require
			pre_open: is_open
			pre_arg_wraped: array.is_wrapped
			pre_no_observers: observers.is_empty
		local
			c: INTEGER
			found: BOOLEAN
		do
			from
				c := 1
			invariant
				linv_open: is_open
				array_wrapped: array.is_wrapped
				found_location: found implies location = c

				c_in_bounds: 1 <= c and c <= array.count + 1
				not_found_before: ∀ i: 1 |..| (c - 1) ¦ array.sequence [i] /= search
				found_before2: found ⇒ array.sequence [c] = search
			until
				c > array.count or found
			loop
				if array [c] = search then
					location := c
					found := True
				else
					c := c + 1
				end
			variant
				array.count - c - if found = False then 0 else 1 end
			end

			if c = array.count + 1 then
				location := -1
			end

			Result := location
		ensure
			mod_def: modify_model ("location", Current)
			post_open: is_open

			not_found: (Result = -1) = (∀ i: 1 |..| array.count ¦ array.sequence [i] /= search)
			found: 1 <= Result and Result <= array.count ⇒ array.sequence [Result] = search
		end

end
