# Specification for _Crowdfunding_ contract

## Top-level specification

The _Crowdfunding_ contract is intended for gathering
assets from community for some useful activity
(such as a product development, event, charity,
volunteering etc.).

The crownfunding campaign works according to the
following rules:
- There is a predefined campaign end date
- There is a target amount to be gathered
- Assets are not accepted before the campaign starts 
and after it ends
- Anytime time upon the campaign ends:
    - In case a target amount has been reached, the
    owner can claim for all the amounts to be
    transferred to him
    - In case a target amount has not been reached,
    and funder can claim for money back

## Graphical specification

Graphically the specification can be represented in
the following way.

![Graphical spec](/Crowdfunding.png)

The present representation is based on actors
(owner and funders), their possible actions and the
expected outcomes of these actions.

## Requirements

### Global requirements

|Code|Description|
|---|---|
|GLO.1|All the balances are not negative|
|GLO.2|The list of possible actions is: initialization, funding, claiming|
|GLO.3|The contract balance equals to the sum of all the gathered fundings|

### Initialization requirements

|Code|Description|
|---|---|
|INI.1|Initialization can be performed only once|
|INI.2|Upon initialization: the contacts becomes initialized, target amount and end date are set up, the list of funders is empty|
|INI.3|The initiator of the initialization becomes an owner|

### Funding

|Code|Description|
|---|---|
|FUN.1|The contract must be iniitialized to accept funding|
|FUN.2|The funder must have the announced amount to get funding accepted|
|FUN.3|The campaign must not be finished to get finding accepted|
|FUN.4|If funding is not accepted the state is not changed|
|FUN.5|If all the conditions above are met: the balance of the funder decreased by the value, the balance of the contract is increased by the value, the funds of the funder are increased by the value, no other balances are changed, no other contract attributes are changed|

### Claiming

|Code|Description|
|---|---|
|CLM.1|The contract must be iniitialized to accept claiming|
|CLM.2|The campaign must be finished to accept claiming|
|CLM.3|If the conditions above are met and target amount is not reached, the sender balance is increased by its funds, its funds become equal to zero and the contract balance is decreased by its funds, no other balances or contract attributes are changed|
|CLM.4|If the conditions above are met and target amount is reached, and the sender is not the owner, the state is not changes|
|CLM.5|If the conditions above are met and target amount is reached, and the sender is the owner, its balance is increased by the contract balance, the contract balance becomes zero, the list of funders becomes empty, no other balances or contract attributes are changed|