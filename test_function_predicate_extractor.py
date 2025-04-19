import re

def extract_predicates_and_functions_from_string(fol_str):
    """
    Extracts potential predicate and function names from a FOL string.

    Uses the heuristic that functions are often used in comparisons,
    while predicates represent standalone truth statements.

    Args:
        fol_str: The string containing the First-Order Logic expression.

    Returns:
        A tuple containing two sets: (predicates, functions).
        Note: This relies on heuristics and may not be perfect for all
              complex or unusually formatted FOL strings. It does not
              perform full parsing.
    """
    predicates = set()
    functions = set()

    # 1. Find all potential calls: identifier followed by parentheses
    potential_calls = re.findall(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*\(([^()]*?)\)', fol_str)

    # Get unique names found in calls
    unique_names = {name for name, args in potential_calls}

    # 2. Define comparison operators (including Unicode variants)
    #    Make sure this includes all operators you might encounter.
    comparison_ops_pattern = r"==?|!=|>=|<=|<|>|≠|≥|≤|=" # Added =, ≥, ≤

    for name in unique_names:
        escaped_name = re.escape(name)

        # 3. Heuristic: Check if this name (when used with args) appears next to a comparison operator.
        #    Looks for `Op name(...)` OR `name(...) Op`
        #    Use non-capturing groups (?:...)
        function_context_pattern = re.compile(
            # Option 1: Comparison Operator followed by name(...)
             # Need whitespace/boundary before Op unless Op is start of string? No, Op needs space usually.
            rf"(?:{comparison_ops_pattern})\s*{escaped_name}\s*\([^()]*?\)"
            # Option 2: name(...) followed by Comparison Operator
            rf"|{escaped_name}\s*\([^()]*?\)\s*(?:{comparison_ops_pattern})"
            , re.UNICODE # Ensure Unicode characters in pattern work correctly
        )

        # Search the *entire* original string for this pattern
        if function_context_pattern.search(fol_str):
            functions.add(name)
        else:
            # If no comparison context is found anywhere for this name, assume it's a predicate
            predicates.add(name)

    # Ensure a name isn't accidentally in both (shouldn't happen with this logic, but safe)
    predicates = predicates - functions

    return predicates, functions

# --- Test ---
fol_str = "(academic_warning(x) ∧ next_term_gpa(x) > 6.5 ∧ ¬violation(x) → lift_warning(x))"
predicates, functions = extract_predicates_and_functions_from_string(fol_str)

print("FOL String:", fol_str)
print("Predicates:", predicates) # Expected: {'eligible_trainer'}
print("Functions:", functions)   # Expected: {'membership_duration'}
