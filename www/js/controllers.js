angular.module('starter.controllers', [])

.controller('AppCtrl', function($scope, $ionicModal, $timeout) {
})

.controller('GrandparentCtrl', function($scope, $log) {
    $scope.predicates = [
        {id: 'ortu_dari', arity: 2},
        //{id: 'eyang_dari', arity: 2}
    ];
    $scope.variablePerms = [
        ['X', 'X'],
        ['X', 'Y'],
        ['X', 'Z'],
        ['Y', 'X'],
        ['Y', 'Y'],
        ['Y', 'Z'],
        ['Z', 'X'],
        ['Z', 'Y'],
        ['Z', 'Z'],
    ];
    $scope.instances = ['candra', 'gilang', 'wati', 'bobi', 'haris', 'eli'];
    $scope.bkgFacts = [
        {predicate: 'ortu_dari', params: ['candra', 'gilang']},
        {predicate: 'ortu_dari', params: ['gilang', 'wati']},
        {predicate: 'ortu_dari', params: ['bobi', 'haris']},
        {predicate: 'ortu_dari', params: ['haris', 'eli']},
    ];
    $scope.posSamples = [
        {params: ['candra', 'wati']},
        {params: ['bobi', 'eli']}
    ];
    $scope.negSamples = [
        {params: ['candra', 'gilang']} // just so we have negative sample
    ];
    $scope.wantedPredicate = 'eyang_dari';
    $scope.wantedPredicateVars = ['X', 'Y'];
    $scope.wantedPredStr = $scope.wantedPredicate + '(' + $scope.wantedPredicateVars.join(', ') + ')';
    $scope.wantedRule = [ // the correct answer
        {predicate: 'ortu_dari', variables: ['X', 'Z']},
        {predicate: 'ortu_dari', variables: ['Z', 'Y']}
    ];
    
    var bodyStrFunc = function(x) { return x.predicate + '(' + x.variables.join(', ') + ')'; };
    var predStrFunc = function(pred) {
        return pred.id + '(' + pred.variables.join(', ') + ') :- '
            + _.map(pred.bodies, bodyStrFunc).join(', ') + '.';
    };
    
    var getPredicateParams = function(body, bindings) {
        // find the resulting params, e.g. for input:
        // variables: [Z, X]
        // bindings: {X: candra, Y: gilang}
        // => params: [null, candra]
        var params = [];
        body.variables.forEach(function(v) {
            if (typeof bindings[v] !== 'undefined') {
                params.push(bindings[v]);
            } else {
                params.push(null);
            }
        });
        return params;
    };
    var getPredicateParamsStr = function(body, bindings) {
        var params = getPredicateParams(body, bindings);
        return body.predicate + '(' + params.join(', ') + ')';
    };
    
    var evalBody = function(body, bindings, bkgFacts) {
        // ask true/false/unknown of the body, given bindings and asserted facts
        // variables: [Z, X]
        // bindings: {X: candra, Y: gilang, Z: bobi}
        // => false
        var myParams = getPredicateParams(body, bindings);
        return _.some(bkgFacts, function(fact) {
            return fact.predicate == body.predicate && _.isEqual(fact.params, myParams);
        });
    };
    
    var learnClauseBodies = function(predicateName, negSamples) {
        var bodies = [];
        // permute variables
        for (var i = 0; i < $scope.variablePerms.length; i++) {
            var l = $scope.variablePerms[i];
            var body = {predicate: predicateName, variables: l};
            // body must NOT match any in negSamples
            var matchedNegs = negSamples.filter(function(negSample) {
                var bindings = {};
                $scope.wantedPredicateVars.forEach(function(varName, varIdx) {
                    bindings[varName] = negSample.params[varIdx];
                });
                var candidateParams = getPredicateParams(body, bindings);
                $log.debug('equals? bindings=', bindings, 'candidateParams=', candidateParams.join(', '), 'negSample=', negSample.params.join(', '));
                return _.isEqual(negSample.params, candidateParams);
            });
            if (matchedNegs.length > 0) {
                $log.debug('wrong body: ', $scope.wantedPredStr, ' :- ',
                           bodyStrFunc(body),
                           'matches', matchedNegs.length, 'negatives:',
                           matchedNegs.map(function(x) { return x.params.join(', '); }));
            } else {
                $log.debug('good body: ', $scope.wantedPredStr, ' :- ',
                           bodyStrFunc(body),
                           'does not match negatives');
                bodies.push(body);
            }
        }
        return bodies;
    };
    
    var tryPred = function(pred, posSamples, bkgFacts) {
        $log.debug('Trying Rule:', predStrFunc(pred), 'using',
                   posSamples.length, 'positive samples');
        posSamples.filter(function(posSample) {
            var bindings = [];
            pred.variables.forEach(function(varName, varIdx) {
                bindings[varName] = posSample.params[varIdx];
            });
            $log.debug('Trying Rule:', predStrFunc(pred), 'using', bindings);
            var evalCounts = _.countBy(pred.bodies, function(body) {
                var zValues = [null]; // don't care about Z
                var unboundZ = _.contains(body.variables, 'Z'); // special case
                if (unboundZ) {
                    // find possible Z values from the background facts
                    zValues = [];
                    bkgFacts.forEach(function(bkgFact) {
                        if (body.predicate == bkgFact.predicate) {
                            if (body.variables[0] != 'Z' && body.variables[1] == 'Z') {
                                if (bindings[body.variables[0]] == bkgFact.params[0]) {
                                    if (!_.contains(zValues, bkgFact.params[1])) {
                                        zValues.push(bkgFact.params[1]);
                                    }
                                }
                            }
                            if (body.variables[1] != 'Z' && body.variables[0] == 'Z') {
                                if (bindings[body.variables[1]] == bkgFact.params[1]) {
                                    if (!_.contains(zValues, bkgFact.params[0])) {
                                        zValues.push(bkgFact.params[0]);
                                    }
                                }
                            }
                        }
                    });
                }
                if (zValues.length > 0) {
                    $log.debug('for body', bodyStrFunc(body), 'z:', zValues);
                    return _.every(zValues, function(z) {
                        bindings['Z'] = z;
                        var truthValue = evalBody(body, bindings, bkgFacts);
                        $log.debug(getPredicateParamsStr(body, bindings), '=>', truthValue);
                        bindings['Z'] = null;
                        return truthValue;
                    });
                } else {
                    return false;
                }
            });
            $log.debug('Rule', predStrFunc(pred), '=>', evalCounts, '/', pred.bodies.length);
            if (evalCounts[true] == pred.bodies.length) {
                $log.debug('VALID Rule', predStrFunc(pred), '=>', evalCounts[true], '/', pred.bodies.length);
            } else {
                $log.debug('INVALID Rule', predStrFunc(pred), '=>', evalCounts[true], '/', pred.bodies.length);
            }
        });
    };
    
    $scope.foil = function() {
        var remainingPosSamples = $scope.posSamples;
        var myPred = {
            id: $scope.wantedPredicate,
            arity: $scope.wantedPredicateVars.length,
            variables: $scope.wantedPredicateVars,
            bodies: []
        };
        var MAX_BODIES = 3; // maximum number of predicate bodies to search
        $scope.predicates.forEach(function(curPred) {
            var bodyPerms = learnClauseBodies(curPred.id, $scope.negSamples);
            $log.debug('Got', bodyPerms.length, 'body permutations:',
                       _.map(bodyPerms, bodyStrFunc));
            bodyPerms.forEach(function(body) {
                myPred.bodies.push(body);
                tryPred(myPred, $scope.posSamples, $scope.bkgFacts);
                // do something
                myPred.bodies.pop();
            });
        });
    };
    
})

;