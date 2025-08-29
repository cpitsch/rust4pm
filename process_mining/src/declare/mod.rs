use std::collections::{HashMap, HashSet};

/// Declare Constraints
/// - LTL Specifications of Constraints are from Di Ciccio et al. "Declarative
///   Process Specifications: Reasoning, Discovery, Monitoring"
///   - The LTL Specifications use LTL enriched with the past with the
///     following symbols and semantics:
///     - `□`: _Always_ in the future
///     - `○`: _Next_
///     - `◇`: _Eventually_
///     - `→`: _Implication_
///     - `♦`: _Previously_ (in the paper, this is a diamond with a line through it)
///     - `⊟`: _Always_ in the past
///     - `⊖`: _Previous_
///     - `U`: _Until_
///     - `S`: _Since_
/// - Regex Specifications are from Di Ciccio et al "Resolving inconsistencies
///   and redundancies in declarative process models"
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declare {
    // Cardinality Templates
    /// "x occurs at least once"
    /// LTL:  `□(start → ◇x)`
    /// Regex: `[^x]*(x[^x]*)+[^x]*`
    AtLeastOne(String),
    /// "x occurs at most once"
    /// LTL:  `□(x → ¬○◇x)`
    /// Regex: `[^x]*(x)?[^x]*`
    AtMostOne(String),

    // Position Templates
    /// "x is the first to occur"
    /// LTL:  `□(start → x)`
    /// Regex: `x.*`
    Init(String),
    /// "x is the last to occur"
    /// LTL:  `□(end → x)`
    /// Regex: `.*x`
    End(String),

    // Forward-unidirectional relation templates
    /// "if x occurs, then y occurs too"
    // LTL:  `□(x → ◇y ∨ ♦y)`
    /// Regex: `[^x]*((x.*y.*) | (y.*x.*))*[^x]*`
    RespondedExistence(String, String),
    /// "if x occurs, then y occurs after x"
    /// LTL: `□(x → ◇y)`
    /// Regex: `[^x]*(x.*y)*[^x]*`
    Response(String, String),
    /// "if x occurs, y occurs afterwards before x recurs"
    /// LTL: `□(x → ○(¬x U y)`
    /// Regex: `[^x]*(x[^x]*y[^x]*)*[^x]*`
    AlternateResponse(String, String),
    /// "if x occurs, y occurs immediately afterwards"
    /// LTL: `□(x → ○y)`
    /// Regex: `[^x]*(xy[^x]*)*[^x]*`
    ChainResponse(String, String),

    // Backward-unidirectional relation templates
    /// "y occurs only if preceded by x"
    /// LTL:  `□(y → ♦x)`
    /// Regex: `[^y]*(x.*y)*[^y]*`
    Precedence(String, String),
    /// "y occurs only if preceded by x with no other y in between"
    /// LTL: `□(y → ⊖(¬y S x))`
    /// Regex: `[^y]*(x[^y]*y[^y]*)*[^y]*`
    AlternatePrecedence(String, String),
    /// "y occurs only if x occurs immediately before it"
    /// LTL: `□(y → ⊖x)`
    /// Regex: `[^y]*(xy[^y]*)*[^y]*`
    ChainPrecedence(String, String),

    // Coupling Templates
    /// "x occurs iff. y occurs"
    /// Regex: `[^xy]*((x.*y.*) | (y.*x.*))*[^xy]*`
    CoExistence(String, String),
    /// "x occurs iff. it is followed by y"
    /// Regex: `[^xy]*(x.*y)*[^xy]*`
    Succession(String, String),
    /// "x and y occur iff. they follow one another, alternating"
    /// Regex: `[^xy]*(x[^xy]*y[^xy]*)*[^xy]*`
    AlternateSuccession(String, String),
    /// "x and y occur iff. y immediately follows x"
    /// Regex: `[^xy]*(xy[^xy]*)*[^xy]*`
    ChainSuccession(String, String),

    // Negative Templates
    /// "x and y occur iff. y does not immediately follow x"
    /// Regex: `[^x]*(xx*[^xy][^x]*)*([^x]*|x)`
    NotChainSuccession(String, String),
    /// "x can never occur before y"
    /// Regex: `[^x]*(x[^y]*)*[^xy]`
    NotSuccession(String, String),
    /// "x and y never co-occur"
    /// Regex: `[^xy]*((x[^y]*) | (y[^x]*))?`
    NotCoExistence(String, String),
}

/// Intermediate representation of a trace used to extract declare constraints
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IntermediateKnowledge {
    /// For each activity, the number of times it occurs in the trace. Contains
    /// all activities, i.e., it contains 0 for activities that did not occur.
    activity_counts: HashMap<String, usize>,
    /// The activities that occurred at least once in the trace. Implied by `activity_counts`,
    /// but used to avoid recomputation for each insert into `first_eventually_precedes`
    seen_activities: HashSet<String>,
    eventually_follows: HashMap<String, Vec<String>>,
    /// The activities that eventually follow the _last_ occurrence of each activity.
    /// For example, for <a,b,a,c>, only c is recorded for a.
    /// In particular, every activity in here eventually follows every occurrence
    /// of this activity in the trace.
    last_eventually_follows: HashMap<String, HashSet<String>>,
    /// The activities that "eventually" precede the _first_ occurrence of each activity.
    first_eventually_precedes: HashMap<String, HashSet<String>>,
    directly_follows: HashMap<String, HashSet<String>>,

    /// Activities found between reoccurences of an activity and between its final
    /// occurrence and the end of the trace. For instance, <a,b,d,a,b,a,e>
    /// gives for activity "a": [{b,d}, {b}, {e}].
    /// TODO: Intersect as we go? Left it "general" (non-intersected) in case
    /// other constraints need more info.
    activities_before_reoccurrence: HashMap<String, Vec<HashSet<String>>>,

    first_activity: Option<String>,
    last_activity: Option<String>,
}

impl IntermediateKnowledge {
    /// Extract the intermediate knowledge from a trace given as a sequence of
    /// activities in a single pass over the trace.
    pub fn extract(trace: &[String], all_activities: &HashSet<String>) -> Self {
        // TODO: If all_activities was a vec, a lot of the HashMaps in here could
        // also be Vecs
        let mut knowledge = Self {
            first_activity: trace.first().cloned(),
            last_activity: trace.last().cloned(),
            activity_counts: all_activities.iter().map(|act| (act.clone(), 0)).collect(),
            ..Default::default()
        };

        let mut last_seen_activity: Option<&str> = None;
        // Remember for each activity when it was last seen.
        let mut last_seen_index: HashMap<&str, usize> = HashMap::default();
        for (index, act) in trace.iter().enumerate() {
            // This activity eventually follows everything we have seen so far.
            knowledge
                .last_eventually_follows
                .values_mut()
                .for_each(|set| {
                    set.insert(act.clone());
                });

            // Nothing eventually follows _this_ occurrence of `act` (yet)
            knowledge
                .last_eventually_follows
                .insert(act.clone(), HashSet::default());

            if *knowledge
                .activity_counts
                .get(act)
                .expect("all_activities contains *all* activities")
                == 0
            {
                // This is the first time we are seeing this activity
                // -> set first_eventually_precedes
                knowledge
                    .first_eventually_precedes
                    .insert(act.clone(), knowledge.seen_activities.clone());
            }

            if let Some(prev_index) = last_seen_index.get(act.as_str()) {
                // Have already seen this activity.
                // TODO: Can we collect these as we go?
                let between: HashSet<String> = trace[*prev_index..index].iter().cloned().collect();
                knowledge
                    .activities_before_reoccurrence
                    .entry(act.clone())
                    .or_default()
                    .push(between);
            }
            last_seen_index.insert(act, index);
            // Start tracking the activities before reocurrence for the new occurrence of act
            // TODO: What if the activity is at the end of the trace. What does this mean
            // for recurrence? For now, we assume that this violates those constraints.
            // (I.e., we keep the empty set at the end)
            knowledge
                .activities_before_reoccurrence
                .entry(act.clone())
                .or_default()
                .push(HashSet::new());

            knowledge
                .activities_before_reoccurrence
                .iter_mut()
                .for_each(|(k, v)| {
                    if k != act {
                        v.last_mut()
                            .expect("All tracked activities are created with an initial HashSet")
                            .insert(act.clone());
                    }
                });

            // TODO: Why not use `knowledge.seen_activities``
            knowledge.activity_counts.iter().for_each(|(k, count)| {
                if *count > 0 {
                    knowledge
                        .eventually_follows
                        .entry(k.clone())
                        .or_default()
                        .push(act.clone());
                }
            });

            if let Some(last_act) = last_seen_activity {
                knowledge
                    .directly_follows
                    .entry(last_act.to_string())
                    .or_default()
                    .insert(act.clone());
            }

            last_seen_activity = Some(act);
            knowledge.seen_activities.insert(act.clone());
            *knowledge
                .activity_counts
                .get_mut(act)
                .expect("all_activities contains *all* activities") += 1;
        }

        knowledge
    }
}

impl Declare {
    // Insertions marked with "trivial by omission" are constraints that hold because
    // the activities do not occur at all. For instance, AtMostOne or RespondedExistence.
    /// Mine all declare constraints that hold for the trace
    ///
    /// * `mine_trivial_by_omission` - Also return constraints that trivially hold because
    ///   activities are _not_ contained in the trace. E.g., "If x occurs then y", and
    ///   x doesn't occur. Defaults to true.
    ///
    /// Currently, the extraction is not implemented for all Declare templates.
    /// The following Declare templates in [`Declare`] are missing:
    ///
    /// - [`AlternatePrecedence`]
    /// - [`AlternateSuccession`]
    /// - [`ChainSuccession`]
    /// - [`NotChainSuccession`]
    /// - [`NotSuccession`]
    /// - [`NotCoExistence`]
    ///
    /// [`AlternatePrecedence`]: Declare::AlternatePrecedence
    /// [`AlternateSuccession`]: Declare::AlternateSuccession
    /// [`ChainSuccession`]: Declare::ChainSuccession
    /// [`NotChainSuccession`]: Declare::NotChainSuccession
    /// [`NotSuccession`]: Declare::NotSuccession
    /// [`NotCoExistence`]: Declare::NotCoExistence
    pub fn mine_trace(
        trace: &[String],
        all_activities: &HashSet<String>,
        mine_trivial_by_omission: Option<bool>,
    ) -> Vec<Self> {
        let mine_trivial_by_omission = mine_trivial_by_omission.unwrap_or(true);
        let knowledge = IntermediateKnowledge::extract(trace, all_activities);
        let mut constraints: Vec<Self> = Vec::new();

        if let Some(act) = knowledge.first_activity {
            constraints.push(Self::Init(act));
        }
        if let Some(act) = knowledge.last_activity {
            constraints.push(Self::End(act));
        }

        knowledge
            .activity_counts
            .into_iter()
            .for_each(|(act, count)| {
                if count > 0 {
                    constraints.push(Self::AtLeastOne(act.clone()));
                }
                if count <= 1 {
                    // INFO: Potentially "trivial by omission" if count is 0
                    constraints.push(Self::AtMostOne(act.clone()))
                }
            });

        constraints.extend(knowledge.seen_activities.iter().flat_map(|a| {
            knowledge.seen_activities.iter().flat_map(|b| {
                [
                    Self::RespondedExistence(a.clone(), b.clone()),
                    Self::CoExistence(a.clone(), b.clone()),
                ]
            })
        }));

        constraints.extend(
            knowledge
                .eventually_follows
                .iter()
                .flat_map(|(a, followers)| {
                    let occurred_before = knowledge
                        .first_eventually_precedes
                        .get(a)
                        .expect("Activity a occurred");

                    followers
                        .iter()
                        .filter(|follower| !occurred_before.contains(*follower))
                        .map(|b| Self::Succession(a.clone(), b.clone()))
                }),
        );

        // Only the activities that eventually follow the last occurrence eventually
        // follow every occurrence
        constraints.extend(
            knowledge
                .last_eventually_follows
                .iter()
                .flat_map(|(a, set)| set.iter().map(|b| Self::Response(a.clone(), b.clone()))),
        );

        // AlternateResponse
        // TODO: I am only considering activities between two occurrences of an
        // activity. I also need to consider all activities after its last occurrence
        constraints.extend(
            knowledge
                .activities_before_reoccurrence
                .iter()
                .flat_map(|(k, v)| {
                    v.iter()
                        .cloned()
                        // Find the activities which are between every pair of occurrences of the activity
                        .reduce(|a, b| a.intersection(&b).cloned().collect())
                        .unwrap()
                        .into_iter()
                        .map(|act| Self::AlternateResponse(k.clone(), act.clone()))
                }),
        );

        constraints.extend(knowledge.directly_follows.iter().filter_map(|(k, values)| {
            (values.len() == 1).then_some(Self::ChainResponse(
                k.clone(),
                values.iter().next().unwrap().clone(),
            ))
        }));

        // Precedence
        constraints.extend(knowledge.first_eventually_precedes.iter().flat_map(
            |(b, preceding)| {
                preceding
                    .iter()
                    .map(|a| Self::Precedence(a.clone(), b.clone()))
            },
        ));

        // TODO: AlternatePrecedence

        let directly_precedes = knowledge
            .directly_follows
            .iter()
            .flat_map(|(k, v)| v.iter().cloned().map(|v| (v, k.clone())))
            .fold(
                HashMap::<String, HashSet<String>>::default(),
                |mut h, (k, v)| {
                    h.entry(k).or_default().insert(v);
                    h
                },
            );

        constraints.extend(directly_precedes.iter().filter_map(|(k, values)| {
            (values.len() == 1).then_some(Self::ChainPrecedence(
                values.iter().next().unwrap().clone(),
                k.clone(),
            ))
        }));

        // TODO: Is vec the right choice? Dont really need a hashset since all
        // are now unique anyways..
        let unseen_activities: Vec<String> = all_activities
            .difference(&knowledge.seen_activities)
            .cloned()
            .collect();

        // INFO: "trivial by omission"
        if mine_trivial_by_omission {
            constraints.extend(unseen_activities.iter().flat_map(|a| {
                all_activities.iter().flat_map(|b| {
                    // If a doesn't occur, then these statements trivially hold.
                    // RespondedExistence also holds if both activities are _not_ in the trace.
                    let constraints = [
                        Self::RespondedExistence(a.clone(), b.clone()),
                        Self::Response(a.clone(), b.clone()),
                        Self::AlternateResponse(a.clone(), b.clone()),
                        Self::ChainResponse(a.clone(), b.clone()),
                        Self::Precedence(b.clone(), a.clone()),
                    ];

                    // Succession only _trivially_ holds if both activities didn't occur
                    let succession = (!knowledge.seen_activities.contains(b))
                        .then(|| Self::Succession(a.clone(), b.clone()));

                    constraints.into_iter().chain(succession)
                })
            }));
        }

        constraints
    }
}

#[cfg(test)]
mod tests {
    //! Many of the tests are from the positive and negative examples in Di Ciccio
    //! et al. "Declarative Process Specifications: Reasoning, Discovery, Monitoring".
    use std::collections::{HashMap, HashSet};

    use itertools::Itertools;

    use super::{Declare, IntermediateKnowledge};

    #[test]
    fn test_declare_knowledge_extraction() {
        let trace = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let all_activities = HashSet::from([
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
        ]);
        let knowledge = IntermediateKnowledge::extract(&trace, &all_activities);

        assert_eq!(
            knowledge,
            IntermediateKnowledge {
                activity_counts: HashMap::from([
                    ("a".to_string(), 1),
                    ("b".to_string(), 1),
                    ("c".to_string(), 1),
                    ("d".to_string(), 0),
                ]),
                seen_activities: HashSet::from(["a".to_string(), "b".to_string(), "c".to_string()]),
                eventually_follows: HashMap::from([
                    ("a".to_string(), vec!["b".to_string(), "c".to_string()]),
                    ("b".to_string(), vec!["c".to_string()]),
                ]),
                // Not interesting since everything occurs only once
                last_eventually_follows: HashMap::from([
                    (
                        "a".to_string(),
                        HashSet::from(["b".to_string(), "c".to_string()])
                    ),
                    ("b".to_string(), HashSet::from(["c".to_string()])),
                    ("c".to_string(), HashSet::new()),
                ]),
                first_eventually_precedes: HashMap::from([
                    ("a".to_string(), HashSet::new()),
                    ("b".to_string(), HashSet::from(["a".to_string()])),
                    (
                        "c".to_string(),
                        HashSet::from(["a".to_string(), "b".to_string()])
                    ),
                ]),
                directly_follows: HashMap::from([
                    ("a".to_string(), HashSet::from(["b".to_string()])),
                    ("b".to_string(), HashSet::from(["c".to_string()])),
                ]),
                // No reoccurences in this trace
                activities_before_reoccurrence: HashMap::new(),
                first_activity: Some("a".to_string()),
                last_activity: Some("c".to_string()),
            }
        )
    }

    #[test]
    fn test_declare_init() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![String::from("a"), String::from("c"), String::from("c")],
            vec![
                String::from("a"),
                String::from("b"),
                String::from("a"),
                String::from("c"),
            ],
        ];
        let negative_examples = [
            vec![String::from("c"), String::from("c")],
            vec![String::from("b"), String::from("a"), String::from("c")],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Init(String::from("a"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Init(String::from("a"))))
        });
    }

    #[test]
    fn test_declare_end() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![String::from("b"), String::from("c"), String::from("a")],
            vec![
                String::from("b"),
                String::from("a"),
                String::from("c"),
                String::from("a"),
            ],
        ];
        let negative_examples = [
            vec![String::from("b"), String::from("c")],
            vec![String::from("b"), String::from("a"), String::from("c")],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::End(String::from("a"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::End(String::from("a"))))
        });
    }

    #[test]
    fn test_declare_at_least_one() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("c"),
            ],
            vec![
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
            ],
        ];
        let negative_examples = [
            vec![String::from("b"), String::from("c"), String::from("c")],
            vec![String::from("c")],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::AtLeastOne(String::from("a"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::AtLeastOne(String::from("a"))))
        });
    }

    #[test]
    fn test_declare_at_most_one() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![String::from("b"), String::from("c"), String::from("c")],
            vec![
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("c"),
            ],
        ];
        let negative_examples = [
            vec![
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
            ],
            vec![
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("a"),
                String::from("a"),
            ],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::AtMostOne(String::from("a"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::AtMostOne(String::from("a"))))
        });
    }

    #[test]
    fn test_declare_responded_existence() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
            ],
            vec![String::from("b"), String::from("c"), String::from("c")],
        ];
        let negative_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
            ],
            vec![String::from("a"), String::from("c"), String::from("c")],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::RespondedExistence(
                    String::from("a"),
                    String::from("b")
                )))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::RespondedExistence(
                    String::from("a"),
                    String::from("b")
                )))
        });
    }

    #[test]
    fn test_declare_response() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
            vec![String::from("b"), String::from("c"), String::from("c")],
        ];
        let negative_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
            ],
            vec![
                String::from("b"),
                String::from("a"),
                String::from("c"),
                String::from("c"),
            ],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Response(String::from("a"), String::from("b"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Response(String::from("a"), String::from("b"))))
        });
    }

    #[test]
    fn test_declare_alternate_response() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
            vec![
                String::from("a"),
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
        ];
        let negative_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
            vec![
                String::from("b"),
                String::from("a"),
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::AlternateResponse(
                    String::from("a"),
                    String::from("b")
                )))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::AlternateResponse(
                    String::from("a"),
                    String::from("b")
                )))
        });
    }

    #[test]
    fn test_declare_chain_response() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("b"),
                String::from("b"),
            ],
            vec![
                String::from("a"),
                String::from("b"),
                String::from("c"),
                String::from("a"),
                String::from("b"),
            ],
        ];
        let negative_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
            vec![String::from("b"), String::from("c"), String::from("a")],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::ChainResponse(
                    String::from("a"),
                    String::from("b")
                )))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::ChainResponse(
                    String::from("a"),
                    String::from("b")
                )))
        });
    }

    #[test]
    fn test_declare_precedence() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
                String::from("b"),
            ],
            vec![String::from("a"), String::from("c"), String::from("c")],
        ];
        let negative_examples = [
            vec![
                String::from("c"),
                String::from("c"),
                String::from("b"),
                String::from("b"),
            ],
            vec![
                String::from("b"),
                String::from("a"),
                String::from("c"),
                String::from("c"),
            ],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Precedence(String::from("a"), String::from("b"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Precedence(String::from("a"), String::from("b"))))
        });
    }

    // #[test]
    // fn test_declare_alternate_precedence() {
    //     let all_activities =
    //         HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
    //     let positive_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("a"),
    //         ],
    //         vec![
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //         ],
    //     ];
    //     let negative_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("b"),
    //             String::from("a"),
    //         ],
    //         vec![
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("b"),
    //         ],
    //     ];
    //
    //     positive_examples.into_iter().for_each(|trace| {
    //         assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::AlternatePrecedence(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    //     negative_examples.into_iter().for_each(|trace| {
    //         assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::AlternatePrecedence(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    // }

    #[test]
    fn test_declare_chain_precedence() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("a"),
                String::from("b"),
                String::from("c"),
                String::from("a"),
            ],
            vec![
                String::from("a"),
                String::from("b"),
                String::from("a"),
                String::from("a"),
                String::from("b"),
                String::from("c"),
            ],
        ];
        let negative_examples = [
            vec![String::from("b"), String::from("c"), String::from("a")],
            vec![
                String::from("b"),
                String::from("a"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
            ],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::ChainPrecedence(
                    String::from("a"),
                    String::from("b")
                )))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::ChainPrecedence(
                    String::from("a"),
                    String::from("b")
                )))
        });
    }

    #[test]
    fn test_declare_co_existence() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
                String::from("b"),
            ],
            vec![
                String::from("b"),
                String::from("c"),
                String::from("c"),
                String::from("a"),
            ],
        ];
        let negative_examples = [
            vec![String::from("c"), String::from("a"), String::from("c")],
            vec![String::from("b"), String::from("c"), String::from("c")],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::CoExistence(String::from("a"), String::from("b"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::CoExistence(String::from("a"), String::from("b"))))
        });
    }

    #[test]
    fn test_declare_succession() {
        let all_activities =
            HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
        let positive_examples = [
            vec![
                String::from("c"),
                String::from("a"),
                String::from("c"),
                String::from("b"),
                String::from("b"),
            ],
            vec![
                String::from("a"),
                String::from("c"),
                String::from("c"),
                String::from("b"),
            ],
            // Copied from the ChainSuccession test, but this is relevant here as
            // well
            vec![String::from("c"), String::from("c"), String::from("c")],
        ];
        let negative_examples = [
            vec![String::from("b"), String::from("a"), String::from("c")],
            vec![
                String::from("b"),
                String::from("c"),
                String::from("c"),
                String::from("a"),
            ],
        ];

        positive_examples.into_iter().for_each(|trace| {
            assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Succession(String::from("a"), String::from("b"))))
        });
        negative_examples.into_iter().for_each(|trace| {
            assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
                .iter()
                .contains(&Declare::Succession(String::from("a"), String::from("b"))))
        });
    }

    // #[test]
    // fn test_declare_alternate_succession() {
    //     let all_activities =
    //         HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
    //     let positive_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("b"),
    //         ],
    //         vec![
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("c"),
    //         ],
    //     ];
    //     let negative_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("b"),
    //         ],
    //         vec![String::from("b"), String::from("a"), String::from("c")],
    //     ];
    //
    //     positive_examples.into_iter().for_each(|trace| {
    //         assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::AlternateSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    //     negative_examples.into_iter().for_each(|trace| {
    //         assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::AlternateSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    // }

    // #[test]
    // fn test_declare_chain_succession() {
    //     let all_activities =
    //         HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
    //     let positive_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("b"),
    //         ],
    //         vec![String::from("c"), String::from("c"), String::from("c")],
    //     ];
    //     let negative_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //         ],
    //         vec![
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("c"),
    //         ],
    //     ];
    //
    //     positive_examples.into_iter().for_each(|trace| {
    //         assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::ChainSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    //     negative_examples.into_iter().for_each(|trace| {
    //         assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::ChainSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    // }

    // #[test]
    // fn test_declare_not_co_existence() {
    //     let all_activities =
    //         HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
    //     let positive_examples = [
    //         vec![
    //             String::from("c"),
    //             String::from("c"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("b"),
    //             String::from("b"),
    //         ],
    //         vec![
    //             String::from("c"),
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("c"),
    //         ],
    //     ];
    //     let negative_examples = [
    //         vec![
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("b"),
    //         ],
    //         vec![
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("c"),
    //         ],
    //     ];
    //
    //     positive_examples.into_iter().for_each(|trace| {
    //         assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::NotCoExistence(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    //     negative_examples.into_iter().for_each(|trace| {
    //         assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::NotCoExistence(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    // }

    // #[test]
    // fn test_declare_not_succession() {
    //     let all_activities =
    //         HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
    //     let positive_examples = [
    //         vec![
    //             String::from("b"),
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("a"),
    //         ],
    //         vec![
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("a"),
    //         ],
    //     ];
    //     let negative_examples = [
    //         vec![
    //             String::from("a"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("b"),
    //         ],
    //         vec![String::from("a"), String::from("b"), String::from("b")],
    //     ];
    //
    //     positive_examples.into_iter().for_each(|trace| {
    //         assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::NotSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    //     negative_examples.into_iter().for_each(|trace| {
    //         assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::NotSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    // }

    // #[test]
    // fn test_declare_not_chain_succession() {
    //     let all_activities =
    //         HashSet::from([String::from("a"), String::from("b"), String::from("c")]);
    //     let positive_examples = [
    //         vec![
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("c"),
    //             String::from("b"),
    //         ],
    //         vec![
    //             String::from("b"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("a"),
    //         ],
    //     ];
    //     let negative_examples = [
    //         vec![
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("b"),
    //         ],
    //         vec![
    //             String::from("c"),
    //             String::from("a"),
    //             String::from("b"),
    //             String::from("c"),
    //         ],
    //     ];
    //
    //     positive_examples.into_iter().for_each(|trace| {
    //         assert!(Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::NotChainSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    //     negative_examples.into_iter().for_each(|trace| {
    //         assert!(!Declare::mine_trace(&trace, &all_activities, Some(true))
    //             .iter()
    //             .contains(&Declare::NotChainSuccession(
    //                 String::from("a"),
    //                 String::from("b")
    //             )))
    //     });
    // }
}
