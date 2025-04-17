import json
import z3
import re
import os
from collections import defaultdict
import sys
import traceback

# --- Thiết lập Logging ---
log_filepath = 'z3_processing_log_v2.txt' # New log file name
try:
    log_file = open(log_filepath, 'w', encoding='utf-8') # Start fresh ('w')
    log_file.write("="*20 + " NEW RUN " + "="*20 + "\n")
except Exception as e:
    print(f"Error opening log file {log_filepath}: {e}. Logging to console instead.")
    log_file = sys.stdout

# Redirect stdout và stderr to log file (hoặc console nếu file lỗi)
original_stdout = sys.stdout
original_stderr = sys.stderr
sys.stdout = log_file
sys.stderr = log_file

print(f"Logging output to: {'Console' if log_file == sys.stdout else log_filepath}")

# --- Hàm load JSON ---
def load_json_dataset(filepath):
    try:
        if not os.path.exists(filepath):
            print(f"Error: File not found at {filepath}")
            return None
        with open(filepath, 'r', encoding='utf-8') as f:
            # Assuming the file contains a single JSON list
            data = json.load(f)
        print(f"Successfully loaded {len(data)} records from {filepath}")
        return data
    except json.JSONDecodeError as json_err:
        print(f"JSON Decode Error in {filepath}: {json_err}. Check file format.")
        return None
    except Exception as e:
        print(f"An error occurred while loading {filepath}: {e}")
        traceback.print_exc(file=log_file)
        return None

# --- Khai báo Sorts và Cache (sẽ được quản lý cho từng sample) ---
Item = z3.DeclareSort('Item')     # Default sort for people, projects, etc.
Degree = z3.DeclareSort('Degree') # Sort for degrees

# Caches - will be cleared for each record
predicate_cache = {}
constant_cache = {}
sort_cache = {'Item': Item, 'Degree': Degree}

# --- Hàm quản lý Symbols (Constants và Predicates) ---

KNOWN_CONSTANTS = {"Sophia", "John", "dr_john", "david", "Alex", "Sarah", "Mary", "PeterGriffin", "Tu", "Tuan", "Kahne", "Coke", "Minh", "Kelvin", "Liam", "Lan", "Mai", "Thao", "Bob", "Dio", "Iruma", "Yashiro", "Ponko", "Ruri", "Ludwig", "Mia"}
KNOWN_DEGREES = {"BA", "MSc", "PhD", "BSc"}
KNOWN_COURSES = {"Calculus1", "Calculus2", "PE1", "PE2", "Subject", "Science_subject", "IT", "BiomedicalEng", "C3", "MA2013", "PH1001", "CH3002", "CH5012", "CH3011", "CO3024", "EE2001", "Chem101", "OrganicChem", "LabSafety", "Biochemistry", "A", "B", "C", "OperatingSystems", "History101", "AdvAlgorithms", "ResearchMethods", "DataStructures", "DiscreteMath", "Capstone", "ML101", "LinearAlgebra", "IntroLinearAlgebra"}
KNOWN_GENERIC_CONSTS = {"faculty", "curriculum", "Mars", "control"} # Thêm các hằng số chung

def get_sort_for_const(name):
    """Determine the sort for a constant."""
    if name in KNOWN_DEGREES:
        return Degree
    # Add more specific rules if needed (e.g., based on context)
    # Default to Item for people, courses, projects etc.
    if name.istitle() or name in KNOWN_CONSTANTS or name in KNOWN_COURSES or name in KNOWN_GENERIC_CONSTS:
         return Item
    # If it's lowercase and not a known category, it might be a variable (handle in parser)
    # or an unknown constant type - default to Item for now
    return Item

def get_constant(name):
    """Lấy hoặc tạo constant Z3 với sort phù hợp."""
    clean_name = name.strip()
    if not clean_name:
        raise ValueError("Constant name cannot be empty")

    sort = get_sort_for_const(clean_name)

    if clean_name not in constant_cache:
        print(f"  Declaring Constant: {clean_name} ({sort.name()})")
        constant_cache[clean_name] = z3.Const(clean_name, sort)
    elif constant_cache[clean_name].sort() != sort:
         print(f"  Warning: Constant '{clean_name}' requested with sort {sort.name()} but already declared with sort {constant_cache[clean_name].sort().name()}. Using existing sort.")
    return constant_cache[clean_name]

# --- Predicate Management ---
PREDEFINED_SIGNATURES = {
    # Signature: Tuple of input sorts + output sort (BoolSort)
    'higher': (Degree, Degree, z3.BoolSort()),
    'has_degree': (Item, Degree, z3.BoolSort()),
    'passed': (Item, Item, z3.BoolSort()), # student, course
    'complete': (Item, Item, z3.BoolSort()), # student, course
    'enroll': (Item, Item, z3.BoolSort()), # student, course
    'can_enroll': (Item, Item, z3.BoolSort()),
    'can_take': (Item, Item, z3.BoolSort()),
    'prereq': (Item, Item, z3.BoolSort()), # course, course
    'Equivalent': (Item, Item, z3.BoolSort()), # course, course
    # Add more based on dataset patterns...
}

def get_predicate(name, arity, sample_args=None):
    """Lấy hoặc tạo predicate Z3. Ưu tiên predefined signatures."""
    clean_name = name.strip()
    if not clean_name:
        raise ValueError("Predicate name cannot be empty")

    cache_key = (clean_name, arity) # Key includes arity

    if cache_key not in predicate_cache:
        print(f"  Defining Predicate: {clean_name} (Arity: {arity})")
        if clean_name in PREDEFINED_SIGNATURES:
            sig = PREDEFINED_SIGNATURES[clean_name]
            expected_arity = len(sig) - 1
            if arity != expected_arity:
                 print(f"  Warning: Predefined signature for '{clean_name}' has arity {expected_arity}, but used with {arity}. Using inferred.")
                 # Fallback to inference
                 arg_sorts = [Item] * arity # Default inference
                 print(f"    Inferred signature: {[s.name() for s in arg_sorts]} -> Bool")
                 predicate_cache[cache_key] = z3.Function(clean_name, *arg_sorts, z3.BoolSort())
            else:
                print(f"    Using predefined signature: {[s.name() for s in sig[:-1]]} -> {sig[-1].name()}")
                predicate_cache[cache_key] = z3.Function(clean_name, *sig)
        else:
             # Simple Inference: Assume 'Item' for all args if not predefined
             arg_sorts = []
             if sample_args: # Try to infer from sample Z3 objects if provided
                 for arg in sample_args:
                      if hasattr(arg, 'sort') and callable(arg.sort):
                           arg_sorts.append(arg.sort())
                      else: # Default if type unknown
                           arg_sorts.append(Item)
                 if len(arg_sorts) != arity: # Fallback if sample args don't match expected arity
                      print(f"   Warning: Sample args count mismatch for {clean_name}. Defaulting sorts.")
                      arg_sorts = [Item] * arity
             else: # Default if no sample args
                  arg_sorts = [Item] * arity

             print(f"    Inferred signature: {[s.name() for s in arg_sorts]} -> Bool")
             predicate_cache[cache_key] = z3.Function(clean_name, *arg_sorts, z3.BoolSort())

    return predicate_cache[cache_key]

# --- Regex-based FOL Parser ---

def parse_predicate_application(text, quantified_vars):
    """Parses P(arg1, arg2, ...)"""
    match = re.match(r"^\s*(\w+)\((.*?)\)\s*$", text)
    if not match:
        # Maybe a 0-ary predicate?
        if re.match(r"^\s*\w+\s*$", text):
             pred_name = text.strip()
             pred_func = get_predicate(pred_name, 0)
             return pred_func()
        print(f"    Error: Cannot parse predicate application '{text}'")
        return None

    pred_name = match.group(1).strip()
    args_str = match.group(2).strip()

    if not args_str: # 0-ary predicate like P() - less common in FOL
        pred_func = get_predicate(pred_name, 0)
        return pred_func()

    # Split arguments carefully, respecting potential structure later
    args = [arg.strip() for arg in args_str.split(',')]
    z3_args = []
    sample_sort_args_for_pred = [] # To help get_predicate infer

    for arg_name in args:
        if arg_name in quantified_vars:
            z3_args.append(quantified_vars[arg_name])
            sample_sort_args_for_pred.append(quantified_vars[arg_name])
        else:
            # Assume it's a constant
            try:
                const = get_constant(arg_name)
                z3_args.append(const)
                sample_sort_args_for_pred.append(const)
            except ValueError:
                print(f"    Error: Unknown term '{arg_name}' in predicate '{pred_name}'")
                return None

    pred_func = get_predicate(pred_name, len(z3_args), sample_args=sample_sort_args_for_pred)
    try:
        return pred_func(*z3_args)
    except z3.Z3Exception as e:
        print(f"    Z3 Type Error applying predicate '{pred_name}' with args {[str(a.sort()) for a in z3_args]} to function {pred_func.decl()}: {e}")
        return None

def parse_expression(text, quantified_vars):
    """Parses potentially nested logical expressions (basic support)."""
    text = text.strip()
    print(f"      Parsing expression: {text}")

    # 1. Handle Negation (Highest precedence after parentheses)
    if text.startswith("¬"):
        inner_expr = parse_expression(text[1:], quantified_vars)
        return z3.Not(inner_expr) if inner_expr else None

    # 2. Handle Parenthesized expressions first
    if text.startswith("(") and text.endswith(")"):
         # Check if it's just wrapping a predicate application like (P(x))
         if re.match(r"^\(\s*\w+\(.*\)\s*\)$", text) or re.match(r"^\(\s*\w+\s*\)$", text):
             # Treat as predicate application
              return parse_predicate_application(text[1:-1], quantified_vars)

         # Try to find main logical connective respecting parentheses
         content = text[1:-1].strip()
         balance = 0
         split_index = -1
         lowest_prec_op = '' # → (lowest), ∨, ∧ (higher)

         # Find the main operator (simplistic, assumes left-to-right grouping for same precedence)
         for i, char in enumerate(content):
             if char == '(': balance += 1
             elif char == ')': balance -= 1
             elif balance == 0:
                 # Check for operators outside inner parentheses
                 if content[i:].startswith('→'):
                      if lowest_prec_op == '':
                          split_index = i
                          lowest_prec_op = '→'
                 elif content[i:].startswith('∨'):
                     if lowest_prec_op == '' or lowest_prec_op == '∨': # → has lower precedence
                          split_index = i
                          lowest_prec_op = '∨'
                 elif content[i:].startswith('∧'):
                      if lowest_prec_op == '' or lowest_prec_op == '∨' or lowest_prec_op == '∧': # →, ∨ have lower/equal precedence
                          split_index = i
                          lowest_prec_op = '∧'


         if lowest_prec_op and split_index != -1:
             left_str = content[:split_index].strip()
             right_str = content[split_index + len(lowest_prec_op):].strip()
             print(f"        Splitting '{content}' by '{lowest_prec_op}' into L:'{left_str}', R:'{right_str}'")

             left_expr = parse_expression(left_str, quantified_vars)
             right_expr = parse_expression(right_str, quantified_vars)

             if left_expr is None or right_expr is None:
                 print(f"        Error parsing operands for '{lowest_prec_op}'")
                 return None

             if lowest_prec_op == '→': return z3.Implies(left_expr, right_expr)
             if lowest_prec_op == '∨': return z3.Or(left_expr, right_expr)
             if lowest_prec_op == '∧': return z3.And(left_expr, right_expr)

         else: # No obvious binary operator, assume predicate application inside parens
              print(f"        No binary operator found or failed split in '{content}', treating as predicate app.")
              return parse_predicate_application(content, quantified_vars)


    # 3. Assume it's a predicate application if no operators/parens found
    else:
        return parse_predicate_application(text, quantified_vars)


def parse_fol_string_to_z3_regex(fol_str_raw):
    fol_str = fol_str_raw.strip()
    print(f"  Parsing FOL (Regex): {fol_str}")

    # Remove outer parentheses if they enclose the entire string
    if fol_str.startswith("(") and fol_str.endswith(")"):
        # Simple check: count parentheses
        if fol_str.count('(') == fol_str.count(')'):
             # More robust check for balancing only outer pair
             balance = 0
             outer_pair = True
             for i, char in enumerate(fol_str):
                 if i == 0: continue
                 if i == len(fol_str) - 1: break
                 if char == '(': balance += 1
                 elif char == ')': balance -= 1
                 if balance < 0: # Closing parenthesis before matching open
                     outer_pair = False
                     break
             if balance == 0 and outer_pair:
                 print(f"    Stripping outer parentheses from: {fol_str}")
                 fol_str = fol_str[1:-1].strip()


    # Pattern: Quantifiers ∀x∀y... ( Body )
    # Allows multiple variables separated by spaces
    quant_pattern = r"^\s*([∀∃])\s*((?:\w+\s*)+)\((.*)\)\s*$"
    match = re.match(quant_pattern, fol_str)
    if match:
        q_type = match.group(1)
        var_names = match.group(2).split()
        body_str = match.group(3).strip()
        print(f"    Matched Quantifier: {q_type} Vars: {var_names} Body: {body_str}")

        z3_vars = {}
        z3_var_list = []
        for var_name in var_names:
             # Infer sort (heuristic)
             var_sort = Item
             if var_name in ['a', 'b', 'c'] and 'higher' in fol_str_raw: var_sort = Degree
             elif var_name == 'd' and ('has_degree' in fol_str_raw or 'higher' in fol_str_raw): var_sort = Degree
             elif var_name in ['h', 'm1', 'm2', 'm3'] : var_sort = Item # Example specific? Need better typing
             # Add more rules if needed
             z3_var = z3.Const(var_name, var_sort)
             z3_vars[var_name] = z3_var
             z3_var_list.append(z3_var)
             print(f"      Declared var: {var_name} ({var_sort.name()})")


        body_expr = parse_expression(body_str, z3_vars)

        if body_expr is not None:
            if q_type == '∀':
                result = z3.ForAll(z3_var_list, body_expr)
                print(f"    --> Parsed ∀: {result}")
                return result
            else: # ∃
                result = z3.Exists(z3_var_list, body_expr)
                print(f"    --> Parsed ∃: {result}")
                return result
        else:
            print(f"    Error parsing body for quantifier.")
            return None

    # Pattern: No quantifier, just an expression
    else:
        print(f"    No quantifier detected, parsing as expression: {fol_str}")
        expr = parse_expression(fol_str, {}) # No quantified variables at this top level
        if expr is not None:
            print(f"    --> Parsed Expression: {expr}")
            return expr
        else:
             print(f"    Warning: Failed to parse non-quantified expression: {fol_str}")
             return None


# --- Hàm Parse Questions (Placeholder, Improved Check) ---
def parse_nl_question(question_nl, premises_z3):
    print(f"  Parsing NL Question: {question_nl[:100]}...")
    goal_expr = None
    q_type = "unknown"
    parsed_data = None # Store either single goal or list of options

    # --- Logic to convert NL to Z3 Goal ---

    # Mẫu: "Does it follow that if all ... P, then all ... Q?"
    q_lower = question_nl.lower()
    match_if_then = re.search(r"if all .* are (\w+), then all .* are (\w+)", q_lower)
    if "does it follow that" in q_lower and match_if_then:
        try:
            # Heuristic names - needs improvement for real NLU
            antecedent_pred_name = match_if_then.group(1).strip().replace(' ', '_').capitalize()
            consequent_pred_name = match_if_then.group(2).strip().replace(' ', '_').capitalize()
            x = z3.Const('q_x', Item)
            # Use arity 1 for these universal statements
            P = get_predicate(antecedent_pred_name, 1, sample_args=[x])
            Q = get_predicate(consequent_pred_name, 1, sample_args=[x])
            parsed_data = z3.Implies(z3.ForAll([x], P(x)), z3.ForAll([x], Q(x)))
            q_type = "yes_no_entailment"
            print(f"    Identified Yes/No Goal: {parsed_data}")
        except Exception as e:
            print(f"    Error parsing Yes/No goal: {e}")
            # traceback.print_exc(file=log_file)

    # Mẫu: "Does [Constant] [Predicate] ...?"
    elif "does" in q_lower and "according to the premises" in q_lower:
        # Try to extract Constant and Predicate (very basic)
        # Example: "Does Sophia qualify for the university scholarship..."
        match_const_pred = re.search(r"does\s+(\w+)\s+(.*?)(?:,|\?|\s+according)", q_lower)
        if match_const_pred:
             const_name = match_const_pred.group(1).strip().capitalize()
             pred_phrase = match_const_pred.group(2).strip().replace(' ', '_')
             try:
                 const = get_constant(const_name)
                 # Assume predicate takes one argument (the constant)
                 pred = get_predicate(pred_phrase, 1, sample_args=[const])
                 parsed_data = pred(const)
                 q_type = "yes_no_fact"
                 print(f"    Identified Yes/No Fact Goal: {parsed_data}")
             except Exception as e:
                 print(f"    Error parsing Yes/No Fact goal for '{const_name}' and '{pred_phrase}': {e}")
                 # traceback.print_exc(file=log_file)
        else:
            print("    Could not match 'Does [Constant] [Predicate]...' pattern.")


    # Mẫu: Multiple Choice "Which conclusion..."
    elif "which conclusion follows" in q_lower or "which is the strongest conclusion" in q_lower or "which is the correct conclusion" in q_lower or "which statement is correct" in q_lower or "what can we conclude" in q_lower or "which capabilities does" in q_lower or "what is the correct conclusion" in q_lower or "what is david’s current eligibility status" in q_lower or "which statement about sarah is correct" in q_lower or "which statement is best supported" in q_lower or "which combination of factors most significantly decreases" in q_lower or "which scenario accurately describes" in q_lower or "which qualifications do all students possess" in q_lower or "which outcomes are guaranteed for all students" in q_lower or "which activities do all students perform" in q_lower or "what affects model performance" in q_lower or "which achievements have all students accomplished" in q_lower:
        options = []
        option_matches = re.findall(r"\n([A-D])\.\s*(.*?)(?=\n[A-D]\.|\Z)", question_nl, re.DOTALL)
        print(f"    Found {len(option_matches)} potential MCQ options.")
        for label, text in option_matches:
            text = text.strip()
            print(f"    Parsing MCQ Option {label}: {text[:80]}...")
            # --- Attempt to parse option text into Z3 (VERY HARD) ---
            option_goal = None
            # Example 1: "If a ... is not P, then it is not Q"
            opt_match_contra = re.match(r"If a .* is not (\w+), then it is not (\w+)", text, re.IGNORECASE)
            if opt_match_contra:
                try:
                    # Make predicate names consistent, e.g., uppercase
                    P_name = opt_match_contra.group(1).strip().upper()
                    Q_name = opt_match_contra.group(2).strip().upper()
                    x = z3.Const(f'mcq_x_{label}', Item) # Unique var name
                    P = get_predicate(P_name, 1, sample_args=[x])
                    Q = get_predicate(Q_name, 1, sample_args=[x])
                    option_goal = z3.ForAll([x], z3.Implies(z3.Not(P(x)), z3.Not(Q(x))))
                    print(f"      Parsed Option Goal (Contrapositive): {option_goal}")
                except Exception as e:
                    print(f"      Error parsing MCQ contrapositive option: {e}")
                    # traceback.print_exc(file=log_file)

            # Example 2: Simple statement about a constant P(c)
            # Very heuristic match, needs refinement
            elif re.match(r"^\w+\s+\w+", text) and any(c in text for c in KNOWN_CONSTANTS):
                 parts = text.split()
                 const_name = None
                 pred_name = None
                 # Try to find known constant
                 for part in parts:
                     cap_part = part.strip(',.').capitalize()
                     if cap_part in KNOWN_CONSTANTS:
                         const_name = cap_part
                         # Try to guess predicate name (e.g., words after constant)
                         try:
                              pred_name = "_".join(parts[parts.index(part)+1:]).strip('.,')
                              break
                         except IndexError: pass
                 if const_name and pred_name:
                     try:
                         const = get_constant(const_name)
                         pred = get_predicate(pred_name, 1, sample_args=[const])
                         option_goal = pred(const)
                         print(f"      Parsed Option Goal (Fact): {option_goal}")
                     except Exception as e:
                         print(f"      Error parsing MCQ fact option: {e}")
                         # traceback.print_exc(file=log_file)
                 else:
                      print(f"      Could not reliably parse fact option: {text}")

            # Example 3: Universal statement All P are Q
            opt_match_all = re.match(r"all\s+.*\s+are\s+(\w+)", text, re.IGNORECASE)
            if opt_match_all and not option_goal: # Only if previous failed
                 try:
                     # Very simple - assumes the last word is the property
                     prop_name = opt_match_all.group(1).strip().upper()
                     x = z3.Const(f'mcq_x_{label}', Item)
                     P = get_predicate(prop_name, 1, sample_args=[x])
                     option_goal = z3.ForAll([x], P(x))
                     print(f"      Parsed Option Goal (Universal): {option_goal}")
                 except Exception as e:
                      print(f"      Error parsing universal option: {e}")


            # Add more parsing rules here for other common option structures
            # ...

            if option_goal is None:
                print(f"      Warning: Could not parse MCQ option text into Z3: {text}")

            options.append({'label': label, 'text': text, 'goal': option_goal})

        if options:
            parsed_data = options
            q_type = "multiple_choice"
        else:
             print(f"    Warning: Could not parse any options for MCQ.")

    # --- Fallback or add more question types ---
    if parsed_data is not None:
         return {'goal_data': parsed_data, 'type': q_type}
    else:
        print(f"    Warning: Could not determine question type or parse NL question into Z3 goal: {question_nl[:100]}...")
        return None


# --- Hàm kiểm tra Logic bằng Z3 ---
def check_entailment(solver, conclusion_expr):
    """Kiểm tra xem kết luận có suy ra từ các tiên đề trong solver không."""
    if conclusion_expr is None or not isinstance(conclusion_expr, (z3.ExprRef, z3.BoolRef)):
        print("      Cannot check entailment: Invalid conclusion expression.")
        return "parse_error"
    try:
        solver.push() # Tạo điểm lưu trạng thái solver
        # print(f"        Checking entailment by adding negation: Not({conclusion_expr})")
        solver.add(z3.Not(conclusion_expr))
        result = solver.check()
        # print(f"        Solver result: {result}")
        solver.pop() # Khôi phục trạng thái solver

        if result == z3.unsat:
            return "Yes" # Phủ định không thỏa mãn -> kết luận đúng
        elif result == z3.sat:
            # Check if the original conclusion is provable (might be contingent)
            # This helps distinguish between "No" (definitely not entailed)
            # and "Maybe" (consistent but not entailed)
            # solver.push()
            # solver.add(conclusion_expr)
            # result_pos = solver.check()
            # solver.pop()
            # if result_pos == z3.unsat: # Should not happen if Not(C) was sat
            #      print("        Inconsistency detected!")
            #      return "Inconsistent_Premises?"
            return "No" # Phủ định thỏa mãn -> kết luận không chắc đúng/không suy ra
        else:
            print(f"        Solver returned unknown/timeout for Not({conclusion_expr})")
            return "Unknown" # Solver không xác định được
    except z3.Z3Exception as e:
        print(f"      Z3Exception during entailment check for {conclusion_expr}: {e}")
        return "solver_error"
    except Exception as e:
        print(f"      Unexpected error during entailment check: {e}")
        traceback.print_exc(file=log_file)
        return "error"

# --- Hàm xử lý chính ---
def process_dataset(data):
    processed_records = []
    stats = {
        "total_records": 0,
        "records_processed": 0,
        "records_skipped": 0,
        "total_premises": 0,
        "premises_parsed": 0,
        "premises_failed": 0,
        "total_questions": 0,
        "questions_parsed": 0,
        "questions_failed_parse": 0,
        "answers_matched": 0,
        "answers_mismatched": 0,
        "answers_uncertain": 0, # Includes parse errors, solver errors, unknowns
    }

    if not data:
        print("Error: No data to process.")
        return [], stats

    stats["total_records"] = len(data)

    for i, record in enumerate(data):
        print(f"\n--- Processing Record {i} ---")
        stats["records_processed"] += 1

        # Basic structure check
        if not isinstance(record, dict) or not all(k in record for k in ['premises-FOL', 'questions', 'answers']):
             print(f"  Skipping record {i}: Invalid format or missing keys.")
             stats["records_skipped"] += 1
             continue

        # Reset caches and solver for each record
        predicate_cache.clear()
        constant_cache.clear()
        solver = z3.Solver()
        print("  Caches and Solver reset.")

        # Rename keys if necessary (handle variations like 'premise-FOL', 'premise-NL')
        premises_fol = record.get('premises-FOL', record.get('premises_fol', []))
        questions_nl = record.get('questions', record.get('questions_nl', []))
        answers_gt = record.get('answers', record.get('answers_gt', []))
        idx_gt = record.get('idx', record.get('indices', record.get('idx_gt', []))) # Handle 'indices' too
        explanation_gt = record.get('explanation', record.get('explanation_gt', []))
        premises_nl = record.get('premises-NL', record.get('premises_nl', [])) # Also get NL premises

        # Ensure lists are lists
        if not isinstance(premises_fol, list): premises_fol = []
        if not isinstance(questions_nl, list): questions_nl = []
        if not isinstance(answers_gt, list): answers_gt = []
        if not isinstance(idx_gt, list): idx_gt = []
        if not isinstance(explanation_gt, list): explanation_gt = []
        if not isinstance(premises_nl, list): premises_nl = []


        processed_record = {
            'original_index': i,
            'premises_nl': premises_nl,
            'premises_fol_str': premises_fol,
            'questions_nl': questions_nl,
            'answers_gt': answers_gt,
            'idx_gt': idx_gt,
            'explanation_gt': explanation_gt,
            'z3_premises': [],
            'parsing_errors': [],
            'inference_results': []
        }


        # Parse Premises
        print(f"  Parsing {len(premises_fol)} Premises...")
        current_premise_errors = 0
        stats["total_premises"] += len(premises_fol)
        for idx, fol_str in enumerate(premises_fol):
            try:
                # Handle variations in FOL key names in nested structures
                if isinstance(fol_str, dict):
                     fol_str_val = fol_str.get('premises-FOL', fol_str.get('premise-FOL', ''))
                else:
                     fol_str_val = fol_str

                if not isinstance(fol_str_val, str) or not fol_str_val.strip():
                     print(f"    Skipping empty or invalid premise string at index {idx}.")
                     continue

                z3_premise = parse_fol_string_to_z3_regex(fol_str_val)
                if z3_premise is not None and isinstance(z3_premise, (z3.ExprRef, z3.BoolRef)):
                    processed_record['z3_premises'].append({'expr': z3_premise, 'original_index': idx + 1})
                    solver.add(z3_premise)
                    stats["premises_parsed"] += 1
                    # print(f"    Added Premise {idx+1}: {z3_premise}") # Verbose
                else:
                    stats["premises_failed"] += 1
                    current_premise_errors += 1
                    error_msg = f"Premise {idx+1}: Failed to parse '{fol_str_val}'"
                    processed_record['parsing_errors'].append(error_msg)
                    print(f"    {error_msg}")
            except Exception as e:
                 stats["premises_failed"] += 1
                 current_premise_errors += 1
                 error_msg = f"Premise {idx+1}: Error parsing '{fol_str}' - {type(e).__name__}: {e}"
                 processed_record['parsing_errors'].append(error_msg)
                 print(f"    {error_msg}")
                 traceback.print_exc(file=log_file)

        if current_premise_errors > 0:
             print(f"  Record {i}: Encountered {current_premise_errors} premise parsing errors.")

        # Parse Questions and Check Logic
        num_questions_in_record = len(questions_nl)
        num_answers_in_record = len(answers_gt)
        stats["total_questions"] += num_questions_in_record
        print(f"  Parsing {num_questions_in_record} Questions and Checking Logic...")

        if num_questions_in_record != num_answers_in_record:
            print(f"  Warning: Mismatch between number of questions ({num_questions_in_record}) and answers ({num_answers_in_record}). Processing up to minimum.")

        for q_idx in range(min(num_questions_in_record, num_answers_in_record)):
            q_nl = questions_nl[q_idx]
            gt_ans = answers_gt[q_idx]

            # Handle nested question structure if present
            if isinstance(q_nl, dict) and 'question' in q_nl:
                 q_text_to_parse = q_nl['question']
                 # Potentially parse choices here if structured like {'question': ..., 'choices': {...}}
            elif isinstance(q_nl, str):
                 q_text_to_parse = q_nl
            else:
                 print(f"    Skipping question {q_idx+1}: Invalid format - {type(q_nl)}")
                 stats["questions_failed_parse"] += 1
                 stats["answers_uncertain"] += 1
                 continue

            parsed_q = parse_nl_question(q_text_to_parse, [p['expr'] for p in processed_record['z3_premises']])
            q_result = "parse_error"
            q_details = {'question_nl': q_text_to_parse, 'ground_truth': gt_ans, 'z3_result': q_result}

            if parsed_q is not None: # Correct check here
                stats["questions_parsed"] += 1
                q_type = parsed_q.get('type', 'unknown')
                goal_data = parsed_q.get('goal_data')

                print(f"    Checking Question {q_idx+1} (Type: {q_type})...")

                if q_type == "yes_no_entailment" or q_type == "yes_no_fact":
                     if goal_data is not None:
                         q_result = check_entailment(solver, goal_data)
                         print(f"      Z3 Result: {q_result}, Ground Truth: {gt_ans}")
                     else:
                         print("      Error: Parsed Yes/No question but goal_data is None.")
                         q_result = "parse_error"

                elif q_type == "multiple_choice":
                    correct_option_found = False
                    best_option = None
                    if isinstance(goal_data, list): # Ensure goal_data is a list of options
                        print(f"    Checking {len(goal_data)} Multiple Choice Options:")
                        for option in goal_data:
                             label = option.get('label', '?')
                             text = option.get('text', '')
                             goal = option.get('goal')
                             print(f"      Checking Option {label}: {text[:60]}...")
                             if goal is not None:
                                 result = check_entailment(solver, goal)
                                 print(f"        Z3 Entailment: {result}")
                                 if result == "Yes":
                                     if not correct_option_found:
                                         best_option = label
                                         correct_option_found = True
                                         print(f"        Potential Answer: {label}")
                             else:
                                 print(f"        Skipping Option {label} due to parsing error.")
                        q_result = best_option if best_option else "No_Option_Valid"
                    else:
                        print("      Error: MCQ goal_data is not a list.")
                        q_result = "parse_error"

                    print(f"      Final MCQ Answer (Z3): {q_result}, Ground Truth: {gt_ans}")
                    q_details['parsed_options'] = goal_data

                else: # Unknown question type
                    print(f"    Skipping question check due to unknown type: {q_type}")
                    q_result = "unknown_type"

            # Update stats based on q_result
            if q_result in ["parse_error", "unknown_type", "solver_error", "error", "No_Option_Valid"]:
                stats["answers_uncertain"] += 1
                if q_result == "parse_error" and parsed_q is None:
                     stats["questions_failed_parse"] += 1

            elif q_result == "Unknown":
                 stats["answers_uncertain"] += 1
            elif isinstance(gt_ans, str) and q_result.lower() == gt_ans.lower():
                 stats["answers_matched"] += 1
            else: # Mismatch
                 stats["answers_mismatched"] += 1
                 print(f"      MISMATCH!")

            q_details['z3_result'] = q_result
            processed_record['inference_results'].append(q_details)


        processed_records.append(processed_record)
        print(f"  Finished processing Record {i}.")

    # --- In Thống kê ---
    print("\n" + "="*10 + " Processing Summary " + "="*10)
    print(f"Total records found: {stats['total_records']}")
    print(f"Records processed: {stats['records_processed']}")
    print(f"Records skipped (invalid format): {stats['records_skipped']}")

    total_premises = stats["premises_parsed"] + stats["premises_failed"]
    if total_premises > 0:
        parse_rate = stats["premises_parsed"] / total_premises if total_premises else 0
        print(f"\nPremises Parsed: {stats['premises_parsed']}/{total_premises} ({parse_rate:.1%})")
        print(f"Premise Parsing Errors: {stats['premises_failed']}")
    else:
         print("\nNo premises encountered.")

    total_questions = stats["total_questions"]
    if total_questions > 0:
        q_parse_rate = stats["questions_parsed"] / total_questions if total_questions else 0
        print(f"\nTotal questions encountered: {total_questions}")
        print(f"Questions Parsed Successfully: {stats['questions_parsed']}/{total_questions} ({q_parse_rate:.1%})")
        print(f"Questions Failed Parse: {stats['questions_failed_parse']}")

        total_checked = stats["answers_matched"] + stats["answers_mismatched"]
        print(f"\nZ3 Answers Matched GT: {stats['answers_matched']}")
        print(f"Z3 Answers Mismatched GT: {stats['answers_mismatched']}")
        print(f"Z3 Answers Uncertain/Error: {stats['answers_uncertain']}")
        match_rate = stats["answers_matched"] / total_checked if total_checked > 0 else 0
        print(f"==> Match Rate (excluding uncertain): {match_rate:.1%}")
    else:
        print("\nNo questions encountered.")

    return processed_records, stats

# --- Chạy chương trình ---
if __name__ == "__main__":
    dataset_filepath = 'train.json'
    if not os.path.exists(dataset_filepath):
         alt_filepath = os.path.join('datasets', 'train.json')
         if os.path.exists(alt_filepath):
              dataset_filepath = alt_filepath
         else:
              print(f"Error: Cannot find dataset file at '{dataset_filepath}' or '{alt_filepath}'.")
              # Try closing log file before exiting
              if log_file != sys.stdout and not log_file.closed: log_file.close()
              sys.exit(1)

    print(f"Using dataset file: {dataset_filepath}")

    raw_data = load_json_dataset(dataset_filepath)

    if raw_data:
        processed_data, summary_stats = process_dataset(raw_data)

        # In chi tiết record đầu tiên (nếu có)
        if processed_data:
            print("\n" + "="*10 + " Sample Processed Record (Index 0 Details) " + "="*10)
            try:
                first_record = processed_data[0]
                print("\nOriginal FOL Strings:", first_record.get('premises_fol_str', 'N/A'))
                print("\nParsed Z3 Premises:")
                for p in first_record.get('z3_premises', []):
                    print(f"  Index {p.get('original_index', '?')}: {p.get('expr', 'N/A')}")
                print("\nParsing Errors:", first_record.get('parsing_errors', []))
                print("\nInference Results:")
                for res_idx, res in enumerate(first_record.get('inference_results', [])):
                    print(f"\n  --- Question {res_idx+1} ---")
                    print(f"  NL: {res.get('question_nl', 'N/A')[:100]}...")
                    print(f"  Ground Truth: {res.get('ground_truth', 'N/A')}")
                    print(f"  Z3 Result:    {res.get('z3_result', 'N/A')}")
                    if 'parsed_options' in res and isinstance(res['parsed_options'], list):
                        print("    Parsed Options (Goals):")
                        for opt in res['parsed_options']:
                             goal_str = str(opt['goal']) if opt['goal'] else "Error/None"
                             print(f"      {opt.get('label', '?')}: {goal_str}")
                    elif 'goal_data' in res and res['type'] != 'multiple_choice':
                         print(f"    Parsed Goal: {res['goal_data']}")

            except IndexError:
                print("  No records were processed successfully to display sample.")
            except Exception as e:
                 print(f"  Error displaying sample record details: {e}")
                 traceback.print_exc(file=log_file)

    else:
        print("Failed to load dataset. Check previous error messages.")

    print(f"\nProcessing complete. Full log potentially available in '{log_filepath}'")

    # Đóng file log nếu nó đang mở
    if log_file != sys.stdout and not log_file.closed:
        log_file.close()

    # Khôi phục stdout/stderr gốc
    sys.stdout = original_stdout
    sys.stderr = original_stderr