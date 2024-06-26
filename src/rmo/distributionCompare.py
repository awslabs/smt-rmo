# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# encode some distribution: KL, Bhattacharyya distance, etc
NEARLY_ZERO = 0.001  # the smallest statistic metric observed in practice is 0.01


def calculate_l0_distance(P: dict, Q: dict):
    # calculate L0 distance
    p, q = normalization(P, Q)
    return max(map(lambda x: abs(x[0] - x[1]), zip(p, q)))


def normalization(P: dict, Q: dict):
    # normalize solver's statistics
    for key in set(P.keys()).union(Q.keys()):
        # Add a relatively small number to avoid possible NaN in the comparison
        if key not in set(P.keys()):
            P.update({key: NEARLY_ZERO})
        if key not in set(Q.keys()):
            Q.update({key: NEARLY_ZERO})
    if P.keys() != Q.keys():
        raise "Errors: they are different distributions and cannot compare"
    P = dict(sorted(P.items(), key=lambda x: x[0]))
    Q = dict(sorted(Q.items(), key=lambda x: x[0]))
    p = list(P.values())
    q = list(Q.values())
    pnorm = []
    qnorm = []

    for pp, qq in zip(p, q):
        pnorm.append((pp + NEARLY_ZERO) / (qq + NEARLY_ZERO))
        qnorm.append(1.0)

    return pnorm, qnorm
