class
	QS_STACK_QUEUE_24

feature {QS_STACK_QUEUE_24}

	stack_plus (stack: QS_STACK_24): INTEGER
		note status: impure
		require
			two_things_on_stack: 2 <= stack.top
			is_wrapped: stack.is_wrapped
		do
			stack.push (stack.pop + stack.pop)
			Result := stack.peek
		ensure
			modify: modify (stack)
			result_is_correct: Result = old (stack.get_elem (stack.top) + stack.get_elem (stack.top - 1))
			size_decreased: stack.size = old stack.size - 1
		end

	stack_minus (stack: QS_STACK_24): INTEGER
		note
			status: impure
		require
			two_things_on_stack: 2 <= stack.top
			is_wrapped: stack.is_wrapped
		do
			stack.push (stack.pop - stack.pop)
			Result := stack.peek
		ensure
			modify: modify (stack)
			size_decreased: stack.size = old stack.size - 1
			result_is_correct: Result = old (stack.get_elem (stack.top) - stack.get_elem (stack.top - 1))
		end

	stack_division (stack: QS_STACK_24): INTEGER
		note
			status: impure
		require
			two_things_on_stack: 2 <= stack.top
			second_elem_non_zero: stack.get_elem (stack.top - 1) /= 0
			is_wrapped: stack.is_wrapped
		do
			stack.push (stack.pop // stack.pop)
			Result := stack.peek
		ensure
			modify: modify (stack)
			size_decreased: stack.size = old stack.size - 1
			result_is_correct: Result = old (stack.get_elem (stack.top) // stack.get_elem (stack.top - 1))
		end

	stack_modulus (stack: QS_STACK_24): INTEGER
		note
			status: impure
		require
			two_things_on_stack: 2 <= stack.top
			is_wrapped: stack.is_wrapped
		do
			stack.push (stack.pop \\ stack.pop)
			Result := stack.peek
		ensure
			modify: modify (stack)
			size_decreased: stack.size = old stack.size - 1
			result_is_correct: Result = old (stack.get_elem (stack.top) \\ stack.get_elem (stack.top - 1))
		end

	queue_plus (queue: QS_QUEUE_24): INTEGER
		note status: impure
		require
			two_things_in_queue: 3 <= queue.rear
			is_wrapped: queue.is_wrapped
		do
			queue.enter (queue.delete + queue.delete)
			Result := queue.get_elem (queue.get_rear - 1)
		ensure
			modify: modify (queue)
			result_is_correct: Result = old (queue.get_elem (queue.front) + queue.get_elem (queue.front + 1))
			size_decreased: queue.size = old queue.size - 1
		end

	queue_minus (queue: QS_QUEUE_24): INTEGER
		note status: impure
		require
			two_things_in_queue: 3 <= queue.rear
			is_wrapped: queue.is_wrapped
		do
			queue.enter (queue.delete - queue.delete)
			Result := queue.get_elem (queue.get_rear - 1)
		ensure
			modify: modify (queue)
			result_is_correct: Result = old (queue.get_elem (queue.front) - queue.get_elem (queue.front + 1))
			size_decreased: queue.size = old queue.size - 1
		end

	queue_division (queue: QS_QUEUE_24): INTEGER
		note status: impure
		require
			non_zero: queue.get_elem (queue.front + 1) /= 0
			two_things_in_queue: 3 <= queue.rear
			is_wrapped: queue.is_wrapped
		do
			queue.enter (queue.delete // queue.delete)
			Result := queue.get_elem (queue.get_rear - 1)
		ensure
			modify: modify (queue)
			result_is_correct: Result = old (queue.get_elem (queue.front) // queue.get_elem (queue.front + 1))
			size_decreased: queue.size = old queue.size - 1
		end

	queue_modulus (queue: QS_QUEUE_24): INTEGER
		note status: impure
		require
			two_things_in_queue: 3 <= queue.rear
			is_wrapped: queue.is_wrapped
		do
			queue.enter (queue.delete \\ queue.delete)
			Result := queue.get_elem (queue.get_rear - 1)
		ensure
			modify: modify (queue)
			result_is_correct: Result = old (queue.get_elem (queue.front) \\ queue.get_elem (queue.front + 1))
			size_decreased: queue.size = old queue.size - 1
		end

	queue_plus_stack (queue: QS_QUEUE_24; stack: QS_STACK_24): INTEGER
		note status: impure
		require
			one_thing_in_queue: queue.rear >= 2
			one_thing_on_stack: stack.top >= 2
			is_wrapped: queue.is_wrapped ∧ stack.is_wrapped
		do
			Result := queue.peek + stack.peek
		ensure
			modify: modify (queue, stack)
			result_is_correct: Result = queue.get_elem (queue.front) + stack.get_elem (stack.top)
		end

	queue_minus_stack (queue: QS_QUEUE_24; stack: QS_STACK_24): INTEGER
		note status: impure
		require
			one_thing_in_queue: queue.rear >= 2
			one_thing_on_stack: stack.top >= 2
			is_wrapped: queue.is_wrapped ∧ stack.is_wrapped
		do
			Result := queue.peek - stack.peek
		ensure
			modify: modify (queue, stack)
			result_is_correct: Result = queue.get_elem (queue.front) - stack.get_elem (stack.top)
		end

	queue_divide_stack (queue: QS_QUEUE_24; stack: QS_STACK_24): INTEGER
		note status: impure
		require
			one_thing_in_queue: queue.rear >= 2
			one_thing_on_stack: stack.top >= 2
			is_wrapped: queue.is_wrapped ∧ stack.is_wrapped
			divisor_not_zero: stack.get_elem (stack.top) /= 0
		do
			Result := queue.peek // stack.peek
		ensure
			modify: modify (queue, stack)
			result_is_correct: Result = queue.get_elem (queue.front) // stack.get_elem (stack.top)
		end

	stack_divide_queue (queue: QS_QUEUE_24; stack: QS_STACK_24): INTEGER
		note status: impure
		require
			one_thing_in_queue: queue.rear >= 2
			one_thing_on_stack: stack.top >= 2
			is_wrapped: queue.is_wrapped ∧ stack.is_wrapped
			divisor_not_zero: queue.get_elem (queue.front) /= 0
		do
			Result := stack.peek // queue.peek
		ensure
			modify: modify (queue, stack)
			result_is_correct: Result = stack.get_elem (stack.top) // queue.get_elem (queue.front)
		end

	queue_modulus_stack (queue: QS_QUEUE_24; stack: QS_STACK_24): INTEGER
		note status: impure
		require
			one_thing_in_queue: queue.rear >= 2
			one_thing_on_stack: stack.top >= 2
			is_wrapped: queue.is_wrapped ∧ stack.is_wrapped
			divisor_not_zero: queue.get_elem (queue.front) /= 0
		do
			Result := queue.peek \\ stack.peek
		ensure
			modify: modify (queue, stack)
			result_is_correct: Result = queue.get_elem (queue.front) \\ stack.get_elem (stack.top)
		end

	stack_modulus_queue (queue: QS_QUEUE_24; stack: QS_STACK_24): INTEGER
		note status: impure
		require
			one_thing_in_queue: queue.rear >= 2
			one_thing_on_stack: stack.top >= 2
			is_wrapped: queue.is_wrapped ∧ stack.is_wrapped
			divisor_not_zero: stack.get_elem (stack.top - 1) /= 0
		do
			Result := stack.peek \\ queue.peek
		ensure
			modify: modify (queue, stack)
			result_is_correct: Result = stack.get_elem (stack.top) \\ queue.get_elem (queue.front)
		end

	driver_stack (stack: QS_STACK_24; op: INTEGER; input: INTEGER): INTEGER
		note
			status: impure
		require
			stack_is_wrapped: stack.is_wrapped
			op_in_range: 0 <= op ∧ op < 9
			op_0: op = 0 ⇒ not stack.is_full
			op_1: op = 1 ⇒ not stack.is_empty
			op_4: op = 4 ⇒ 2 <= stack.top
			op_5: op = 5 ⇒ 2 <= stack.top
			op_6: op = 6 ⇒ (2 <= stack.top ∧… stack.get_elem (stack.top - 1) /= 0)
			op_7: op = 7 ⇒ (2 <= stack.top ∧… stack.get_elem (stack.top - 1) /= 0)
		do
			Result := 0
			inspect op
			when 0 then stack.push (input)
			when 1 then Result := stack.pop
			when 2 then Result := stack.search (input)
			when 3 then Result := if stack.is_contain (input) then 1 else 0 end
			when 4 then Result := stack_plus (stack)
			when 5 then Result := stack_minus (stack)
			when 6 then Result := stack_division (stack)
			when 7 then Result := stack_modulus (stack)
			else Result := stack.size end
			Result := Result
		ensure
			modifies_stack: modify (stack)
			op_0: op = 0 ⇒ stack.get_elem (stack.top) = input ∧ stack.top = (old stack.top + 1) ∧ Result = 0
			op_1: op = 1 ⇒ Result = (old stack.get_elem (stack.top)) ∧ stack.top = old stack.top - 1
			op_2_found: op = 2 ∧ 1 <= Result ∧ Result <= stack.top ⇒ input = stack.get_elem (Result)
			op_2_not_found: op = 2 ∧ Result = -1 ⇒ ∀ i: 1 |..| stack.top ¦ stack.arr.sequence [i] /= input
			op_3_exists: op = 3 ∧ Result = 1 ⇒ ∃ i: 1 |..| stack.top ¦ stack.arr.sequence [i] = input
			op_3_not_exists: op = 3 ∧ Result = 0 ⇒ ∀ i: 1 |..| stack.top ¦ stack.arr.sequence [i] /= input
			op_4_correct: op = 4 ⇒ Result = old (stack.get_elem (stack.top) + stack.get_elem (stack.top - 1))
			op_4_size_decreased: op = 4 ⇒ stack.size = old stack.size - 1
			op_5_correct: op = 5 ⇒ Result = old (stack.get_elem (stack.top) - stack.get_elem (stack.top - 1))
			op_5_size_decreased: op = 5 ⇒ stack.size = old stack.size - 1
			op_6_correct: op = 6 ⇒ Result = old (stack.get_elem (stack.top) // stack.get_elem (stack.top - 1))
			op_6_size_decreased: op = 6 ⇒ stack.size = old stack.size - 1
			op_7_correct: op = 7 ⇒ Result = old (stack.get_elem (stack.top) \\ stack.get_elem (stack.top - 1))
			op_7_size_decreased: op = 7 ⇒ stack.size = old stack.size - 1
			op_8_correct: op = 8 ⇒ Result = stack.top
		end

	driver_queue (queue: QS_QUEUE_24; op: INTEGER; input: INTEGER): INTEGER
		note
			status: impure
		require
			queue_is_wrapped: queue.is_wrapped
			op_in_range: 0 <= op ∧ op < 9
			op_0: op = 0 ⇒ not queue.is_full
			op_1: op = 1 ⇒ not queue.is_empty
			op_4: op = 4 ⇒ 3 <= queue.rear
			op_5: op = 5 ⇒ 3 <= queue.get_rear
			op_6: op = 6 ⇒ (3 <= queue.rear ∧… queue.get_elem (queue.front + 1) /= 0)
			op_7: op = 7 ⇒ (3 <= queue.rear ∧… queue.get_elem (queue.front + 1) /= 0)
		do
			Result := 0
			inspect op
			when 0 then queue.enter (input)
			when 1 then Result := queue.delete
			when 2 then Result := queue.search (input)
			when 3 then Result := if queue.is_contain (input) then 1 else 0 end
			when 4 then Result := queue_plus (queue)
			when 5 then Result := queue_minus (queue)
			when 6 then Result := queue_division (queue)
			when 7 then Result := queue_modulus (queue)
			else Result := queue.size end
			Result := Result
		ensure
			modifies_queue: modify (queue)
			op_0: op = 0 ⇒ queue.get_elem (queue.rear - 1) = input ∧ queue.rear - 1 = (old queue.rear) ∧ Result = 0
			op_1_rear_decreased: op = 1 ⇒ queue.rear = old queue.rear - 1
			op_1_result_correct: op = 1 ⇒ Result = old (queue.queue.sequence [queue.front])
			op_1_queue_shifted: op = 1 ⇒ ∀ i: 1 |..| (queue.rear - 1) ¦ queue.queue.sequence [i] = (old queue.queue.sequence) [i + 1]
			op_2_found: op = 2 ∧ 1 <= Result ∧ Result < queue.rear ⇒ queue.queue.sequence [Result] = input
			op_2_not_found: op = 2 ∧ Result = -1 ⇒ ∀ i: 1 |..| (queue.rear - 1) ¦ queue.queue.sequence [i] /= input
			op_3_found: op = 3 ∧ Result = 1 ⇒ ∃ i: 1 |..| (queue.rear - 1) ¦ queue.queue.sequence [i] = input
			op_3_not_found: op = 3 ∧ Result = 0 ⇒ ∀ i: 1 |..| (queue.rear - 1) ¦ queue.queue.sequence [i] /= input
			op_4_result_correct: op = 4 ⇒ Result = old (queue.get_elem (queue.front) + queue.get_elem (queue.front + 1))
			op_4_size_decreased: op = 4 ⇒ queue.size = old (queue.size - 1)
			op_5_result_correct: op = 5 ⇒ Result = old (queue.get_elem (queue.front) - queue.get_elem (queue.front + 1))
			op_5_size_decreased: op = 5 ⇒ queue.size = old (queue.size - 1)
			op_6_result_correct: op = 6 ⇒ Result = old (queue.get_elem (queue.front) // queue.get_elem (queue.front + 1))
			op_6_size_decreased: op = 6 ⇒ queue.size = old (queue.size - 1)
			op_7_result_correct: op = 7 ⇒ Result = old (queue.get_elem (queue.front) \\ queue.get_elem (queue.front + 1))
			op_7_size_decreased: op = 7 ⇒ queue.size = old (queue.size - 1)
			op_8_result_correct: op = 8 ⇒ Result = queue.rear - 1
		end

	driver_queue_stack (stack: QS_STACK_24; queue: QS_QUEUE_24; op: INTEGER): INTEGER
		note
			status: impure
		require
			are_wrapped: stack.is_wrapped ∧ queue.is_wrapped
			op_in_range: op = 0 or op = 5
			op_0: op = 0 ⇒ 2 <= queue.rear ∧ 2 <= stack.top
			op_1: op = 1 ⇒ 2 <= queue.rear ∧ 2 <= stack.top
			op_2: op = 2 ⇒ 2 <= queue.rear ∧ 2 <= stack.top
			op_2_input: op = 2 ⇒ stack.get_elem (stack.top - 1) /= 0
			op_3: op = 3 ⇒ 2 <= queue.rear ∧ 2 <= stack.top
			op_3_input: op = 3 ⇒ queue.get_elem (queue.front) /= 0
			op_4: op = 4 ⇒ 2 <= queue.rear ∧ 2 <= stack.top
			op_4_input: op = 4 ⇒ stack.get_elem (stack.top - 1) /= 0
			op_5: op = 5 ⇒ 2 <= queue.rear ∧ 2 <= stack.top
			op_5_input: op = 5 ⇒ stack.get_elem (stack.top - 1) /= 0
		local
			sq: QS_STACK_QUEUE_24
		do
			create sq
			Result := 0
			inspect op
			when 0 then Result := sq.queue_plus_stack (queue, stack)
			when 1 then Result := sq.queue_minus_stack (queue, stack)
			when 2 then Result := sq.queue_divide_stack (queue, stack)
			when 3 then Result := sq.stack_divide_queue (queue, stack)
			when 4 then Result := sq.queue_modulus_stack (queue, stack)
			else Result := sq.stack_modulus_queue (queue, stack) end
			Result := Result
		ensure
			modifies: modify (stack, queue)
			op_0: op = 0 ⇒ Result = queue.get_elem (queue.front) + stack.get_elem (stack.top)
			op_1: op = 1 ⇒ Result = queue.get_elem (queue.front) - stack.get_elem (stack.top)
			op_2: op = 2 ⇒ Result = queue.get_elem (queue.front) // stack.get_elem (stack.top)
			op_3: op = 3 ⇒ Result = stack.get_elem (stack.top) // queue.get_elem (queue.front)
			op_4: op = 4 ⇒ Result = queue.get_elem (queue.front) \\ stack.get_elem (stack.top)
			op_5: op = 5 ⇒ Result = stack.get_elem (stack.top) \\ queue.get_elem (queue.front)
		end
end
