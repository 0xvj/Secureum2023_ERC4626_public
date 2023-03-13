using DummyERC20A as ERC20a 
using DummyERC20B as ERC20b 

methods {
    name() returns string envfree;
    symbol() returns string envfree;
    decimals() returns uint8 envfree;
    asset() returns address envfree;

    totalSupply() returns uint256 envfree;
    allowance(address,address) returns uint256 envfree; 
    balanceOf(address) returns uint256 envfree => DISPATCHER(true);
    nonces(address) returns uint256 envfree;

    approve(address,uint256) returns bool;
    transfer(address,uint256) returns bool => DISPATCHER(true);
    transferFrom(address,address,uint256) returns bool => DISPATCHER(true);
    deposit(uint256,address);
    mint(uint256,address);
    withdraw(uint256,address,address);
    redeem(uint256,address,address);

    totalAssets() returns uint256 envfree;
    userAssets(address) returns uint256 envfree;
    convertToShares(uint256) returns uint256 envfree;
    convertToAssets(uint256) returns uint256 envfree;
    previewDeposit(uint256) returns uint256 envfree;
    previewMint(uint256) returns uint256 envfree;
    previewWithdraw(uint256) returns uint256 envfree;
    previewRedeem(uint256) returns uint256 envfree;

    maxDeposit(address) returns uint256 envfree;
    maxMint(address) returns uint256 envfree;
    maxWithdraw(address) returns uint256 envfree;
    maxRedeem(address) returns uint256 envfree;

    permit(address,address,uint256,uint256,uint8,bytes32,bytes32);
    DOMAIN_SEPARATOR() returns bytes32;

    ERC20a.balanceOf(address) returns uint256 envfree;
    ERC20a.totalSupply() returns uint256 envfree;
    ERC20b.totalSupply() returns uint256 envfree;
    ERC20a.allowance(address,address) returns uint256 envfree;
    
}


function safeAssumptions(env e) {
    require asset() != currentContract; 
    require e.msg.sender != currentContract;
}

// state
definition shareHolder(address user) returns bool = balanceOf(user) > 0;


// ghost and hook
ghost mathint sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

hook Sload uint256 val balanceOf[KEY address addy] STORAGE {
    require sumOfBalances >= val;
}


ghost mathint sumOfBalancesERC20a {
    init_state axiom sumOfBalancesERC20a == 0;
}

hook Sstore ERC20a.b[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalancesERC20a = sumOfBalancesERC20a + newValue - oldValue;
}

hook Sload uint256 val ERC20a.b[KEY address addy] STORAGE {
    require sumOfBalancesERC20a >= val;
}


ghost mathint sumOfBalancesERC20b {
    init_state axiom sumOfBalancesERC20b == 0;
}

hook Sstore ERC20b.b[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalancesERC20b = sumOfBalancesERC20b + newValue - oldValue;
}

hook Sload uint256 val ERC20b.b[KEY address addy] STORAGE {
    require sumOfBalancesERC20b >= val;
}


// VALID-STATES

// invariant
// Property: totalSupply integrity (totalSupply should always be equal to sum of balances)
invariant totalSupplyIsSumOfBalances()
    totalSupply() == sumOfBalances

// Property: Assets totalSupply should always be equal to sum of balance
invariant ERC20aTotalSupplyIsSumOfBalances()
    ERC20a.totalSupply() == sumOfBalancesERC20a


invariant ERC20bTotalSupplyIsSumOfBalances()
    ERC20b.totalSupply() == sumOfBalancesERC20b

// Property: totalSupply should always less than equal to totalAssets
invariant totalSupplyAlwaysLessThanOrEqualTotalAssets()
    totalSupply() <= totalAssets() 
    {
        preserved with(env e){
            require e.msg.sender != currentContract;
            requireInvariant totalSupplyIsSumOfBalances();
        }
    }


// HIGH-LEVEL PROPERTIES 

// Property: System is always solvent
invariant systemIsAlwaysSolvent()
    // totalSupply() > 0 => totalAssets() > 0 &&
    totalAssets() == 0 =>totalSupply() == 0
    {
        preserved {
            requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();
            requireInvariant totalSupplyIsSumOfBalances();
        }
    }


// UNIT-TESTS
// Deposit Unit Test

rule depositUnitTest(env e,uint assets,address receiver){

    // safeAssumptions();
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

    uint assetsBefore = userAssets(e.msg.sender);
    uint receiverSharesBefore = balanceOf(receiver);
    uint totalSupplyBefore = totalSupply();
    uint totalAssetsBefore = totalAssets();
    
    uint shares = deposit(e,assets,receiver);

    uint assetsAfter = userAssets(e.msg.sender);
    uint receiverSharesAfter = balanceOf(receiver);
    uint totalSupplyAfter = totalSupply();
    uint totalAssetsAfter = totalAssets();

    assert shares <= assets,
        "shares minted should always be less than assets deposited";

    assert receiverSharesAfter == receiverSharesBefore + shares,
        "Receiver's shares changed by wrong amount";

    assert e.msg.sender != currentContract => assetsAfter == assetsBefore - assets,
        "msg.sender's assets changed by wrong amount";

    assert totalSupplyAfter == totalSupplyBefore + shares,
        "Total Supply changed by a wrong amount";

    assert e.msg.sender != currentContract => totalAssetsAfter == totalAssetsBefore + assets,
        "Vault assets changed by a wrong amount after deposit";

}


// rule depositRevertConditions(env e, uint assets , address receiver) {

//     requireInvariant totalSupplyIsSumOfBalances();
//     requireInvariant assetTotalSupplyIsSumOfBalances();
//     requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

//     address owner;
//     withdraw@withrevert(e,assets,receiver,owner);
//     bool withdrawReverted = lastReverted;

//     uint assetsBefore = ERC20a.balanceOf(e.msg.sender);
//     uint allowanceBefore = ERC20a.allowance(e.msg.sender,currentContract);
//     uint shares = convertToShares(assets);

//     deposit@withrevert(e,assets,receiver);

//     assert !withdrawReverted => (lastReverted <=> ( shares == 0 
//         || assetsBefore < assets 
//         || allowanceBefore < assets 
//     )), "deposit must revert if and only if above conditions are satisfied";

// }


rule mintUnitTest(env e,uint shares,address receiver){

    safeAssumptions(e);
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();


    uint assetsBefore = userAssets(e.msg.sender);
    uint receiverSharesBefore = balanceOf(receiver);
    uint totalSupplyBefore = totalSupply();

    uint assets = mint(e,shares,receiver);

    uint assetsAfter = userAssets(e.msg.sender);
    uint receiverSharesAfter = balanceOf(receiver);
    uint totalSupplyAfter = totalSupply();

    assert shares <= assets,
        "shares minted should always be less than assets deposited";

    assert receiverSharesAfter == receiverSharesBefore + shares,
        "Receiver's shares changed by wrong amount";

    assert e.msg.sender != currentContract => assetsAfter == assetsBefore - assets,
        "msg.sender's assets changed by wrong amount";
    
    assert totalSupplyAfter == totalSupplyBefore + shares,
        "Total Supply changed by a wrong amount";

}

// rule mintRevertConditions(env e, uint shares , address receiver) {

//     requireInvariant totalSupplyIsSumOfBalances();
//     requireInvariant assetTotalSupplyIsSumOfBalances();
//     requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

//     address owner;
//     redeem@withrevert(e,shares,receiver,owner);

//     bool redeemReverted = lastReverted;

//     uint assetsBefore = ERC20a.balanceOf(e.msg.sender);
//     uint allowanceBefore = ERC20a.allowance(e.msg.sender,currentContract);
//     uint assets = previewMint(shares);

//     mint@withrevert(e,shares,receiver);

//     assert !redeemReverted => (lastReverted <=> ( 
//          assetsBefore < assets 
//         || allowanceBefore < assets 
//     )), "mint must revert if and only if above conditions are satisfied";
// }



rule withdrawUnitTest(env e,uint assets,address receiver,address owner) {

    safeAssumptions(e);
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();
    
    uint totalAssetsBefore = totalAssets();
    uint receiverAssetsBefore = userAssets(receiver);
    uint ownerSharesBefore    = balanceOf(owner);
    uint totalSupplyBefore = totalSupply();
    uint allowanceBefore = allowance(owner,e.msg.sender);
    
    uint shares = withdraw(e,assets,receiver,owner);

    uint totalAssetsAfter = totalAssets();
    uint receiverAssetsAfter = userAssets(receiver);
    uint ownerSharesAfter    = balanceOf(owner);
    uint totalSupplyAfter = totalSupply();
    uint allowanceAfter = allowance(owner,e.msg.sender);

    assert receiver != currentContract => totalAssetsAfter == totalAssetsBefore - assets,
        "total assets of the system changed by wrong amount after withdrawal";

    assert shares <= assets,
        "shares bured should always be less than assets withdrawn";

    assert receiver != currentContract => receiverAssetsAfter == receiverAssetsBefore + assets,
        "Receiver assets changed by wrong amount after withdraw";

    assert ownerSharesAfter == ownerSharesBefore - shares,
        "Owner shares changed by wrong amount after withdraw";

    assert totalSupplyAfter == totalSupplyBefore - shares,
        "Total Supply changed by a wrong amount";
    
    // This thing is found during bug injection phase
    assert e.msg.sender != owner  => (allowanceBefore != max_uint256 => allowanceAfter == allowanceBefore - shares),
        "msg.sender's allowance of owner changed by wrong amount";
}


// rule withdrawRevertConditions(env e,uint assets,address receiver,address owner) {
    
//     requireInvariant totalSupplyIsSumOfBalances();
//     requireInvariant assetTotalSupplyIsSumOfBalances();

//     deposit@withrevert(e,assets,receiver);
//     bool depositReverted = lastReverted;

//     uint sharesBefore = balanceOf(owner);
//     uint assetsBefore = previewWithdraw(sharesBefore);
//     uint allowanceBefore    = allowance(owner,e.msg.sender);

//     withdraw@withrevert(e,assets,receiver,owner);

//     assert !depositReverted => (lastReverted <=> assetsBefore < assets
//         || allowanceBefore < assets
//     ),"withdraw must revert if and only if above conditions are satisfied";

// }



rule redeeemUnitTest(env e , uint shares,address receiver,address owner) {

    safeAssumptions(e);
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

    uint totalAssetsBefore = totalAssets();
    uint receiverAssetsBefore = userAssets(receiver);
    uint ownerSharesBefore    = balanceOf(owner);
    uint totalSupplyBefore = totalSupply();
    uint allowanceBefore = allowance(owner,e.msg.sender);

    uint assets = redeem(e,shares,receiver,owner);

    uint totalAssetsAfter = totalAssets();
    uint receiverAssetsAfter = userAssets(receiver);
    uint ownerSharesAfter    = balanceOf(owner);
    uint totalSupplyAfter = totalSupply();
    uint allowanceAfter = allowance(owner,e.msg.sender);

    assert receiver != currentContract => totalAssetsAfter == totalAssetsBefore - assets,
        "total assets of the system changed by wrong amount after withdrawal";

    assert shares <= assets,
        "shares bured should always be less than assets withdrawn";

    assert receiver != currentContract => receiverAssetsAfter == receiverAssetsBefore + assets,
        "Receiver assets changed by wrong amount after withdraw";
    
    assert ownerSharesAfter == ownerSharesBefore - shares,
        "Owner shares changed by wrong amount after withdraw";

    assert totalSupplyAfter == totalSupplyBefore - shares,
        "Total Supply changed by a wrong amount";

    // This thing is found during bug injection phase
    assert e.msg.sender != owner  => (allowanceBefore != max_uint256 => allowanceAfter == allowanceBefore - shares),
        "msg.sender's allowance of owner changed by wrong amount";

    assert e.msg.sender == owner  => allowanceAfter == allowanceBefore,
        "msg.sender's allowance of owner changed by wrong amount";
    
}

// rule redeemRevertConditions(env e,uint shares,address receiver) {
    
// }



// VARIABLE TRANSITIONS

rule onlyOwnerOrAlloweeCanTakeOutAssets(env e, method f,calldataarg arg) {

    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

    address user;
    uint sharesBefore = balanceOf(user);
    uint senderAllowance = allowance(user,e.msg.sender);

    f(e,arg);

    uint sharesAfter     = balanceOf(user);
    
    assert sharesAfter < sharesBefore => (e.msg.sender == user || senderAllowance > 0),
        "Assets of user take out from the vault by another user who doesn't have allowance";
}

rule alloweeCanOnlyTakeOutAllowedNumberOfShares(env e, method f,calldataarg arg) {

    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

    address user;
    uint sharesBefore = balanceOf(user);
    uint senderAllowance = allowance(user,e.msg.sender);

    f(e,arg);

    uint sharesAfter     = balanceOf(user);
    mathint sharesWithdrawn = sharesBefore - sharesAfter;

    assert sharesWithdrawn > 0 && e.msg.sender != user => (senderAllowance >= sharesWithdrawn),
        "Allowee withdrawn more than allowed shares";
}

rule vaultAssetCannotbeChanged(env e,method f,calldataarg arg) {

    uint assetBefore = asset();

    f(e,arg);

    uint assetAfter = asset();

    assert assetBefore == assetAfter,
        "Vault asset cannot be changed";
}

rule balanceOfUserCanOnlyChangedByFewFunctions(env e,method f,calldataarg arg) {

    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();

    address user;
    uint sharesBefore = balanceOf(user);
    f(e,arg);
    uint sharesAfter = balanceOf(user);

    assert sharesAfter < sharesBefore => (f.selector == withdraw(uint256,address,address).selector
        || f.selector == redeem(uint256,address,address).selector
        || f.selector == transfer(address,uint256).selector
        || f.selector == transferFrom(address,address,uint256).selector
    ),"Shares of a user can only decreased by above functions";

    assert sharesAfter > sharesBefore => (f.selector == deposit(uint256,address).selector
        || f.selector == mint(uint256,address).selector
        || f.selector == transfer(address,uint256).selector
        || f.selector == transferFrom(address,address,uint256).selector
    ),"Shares of a user can only increased by above functions";
}

rule totalSupplyCanOnlyChangedByFewFunctions(env e,method f,calldataarg arg) {

    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();

    uint totalSupplyBefore = totalSupply();

    f(e,arg);

    uint totalSupplyAfter = totalSupply();


    assert totalSupplyAfter < totalSupplyBefore => (f.selector == withdraw(uint256,address,address).selector
        || f.selector == redeem(uint256,address,address).selector
    ),"Shares of a user can only decreased by above functions";

    assert totalSupplyAfter > totalSupplyBefore => (f.selector == deposit(uint256,address).selector
        || f.selector == mint(uint256,address).selector
    ),"Shares of a user can only decreased by above functions";
}





rule integrityOfTotalSupplyAndTotalAssets(env e,method f,calldataarg arg) {
    
    require asset() != currentContract;
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();


    require totalSupply() == sumOfBalances;
    require ERC20a.totalSupply() == sumOfBalancesERC20a;

    uint assetsBefore = totalAssets();
    uint sharesBefore = totalSupply();

    f(e,arg);

    uint assetsAfter = totalAssets();
    uint sharesAfter = totalSupply();


    assert sharesAfter > 0 => assetsAfter > 0;
    assert assetsAfter == 0 => sharesAfter == 0;

}


rule monotonicityOfSharesAndAssets(env e, method f,calldataarg arg) {
    require asset() != currentContract;
    require e.msg.sender != currentContract;

    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();


    uint assetsBefore = totalAssets();
    uint sharesBefore = totalSupply();

    if(f.selector ==  withdraw(uint256,address,address).selector) {
        uint assets;
        address receiver;
        address owner;
        require receiver != currentContract;
        withdraw(e,assets,receiver,owner);
    } else if(f.selector ==  redeem(uint256,address,address).selector) {
        uint shares;
        address receiver;
        address owner;
        require receiver != currentContract;
        redeem(e,shares,receiver,owner);
       
    } else 
        f(e,arg);

    uint assetsAfter = totalAssets();
    uint sharesAfter = totalSupply();

    assert sharesAfter > sharesBefore <=> assetsAfter > assetsBefore;
    assert sharesAfter == sharesBefore <=> assetsAfter == assetsBefore;
    assert sharesAfter < sharesBefore <=> assetsAfter < assetsBefore;

}

rule antiMonotonicityOfUserAssetsAndVaultAssets(env e, method f,calldataarg arg) {

    address user;   
    require user != currentContract;
    require e.msg.sender == user;

    uint userBalanceBefore  = ERC20a.balanceOf(user);
    uint vaultBalanceBefore = ERC20a.balanceOf(currentContract);

    if(f.selector == withdraw(uint256,address,address).selector) {
        uint assets;
        address receiver = user;
        address owner;
        withdraw(e,assets,receiver,owner);

    } else if(f.selector == redeem(uint256,address,address).selector) {
        uint shares;
        address receiver = user;
        address owner;
        redeem(e,shares,receiver,owner);

    } else 
        f(e,arg);

    uint userBalanceAfter  = ERC20a.balanceOf(user);
    uint vaultBalanceAfter = ERC20a.balanceOf(currentContract);

    assert userBalanceAfter < userBalanceBefore  <=> vaultBalanceAfter > vaultBalanceBefore;
    assert userBalanceAfter > userBalanceBefore  <=> vaultBalanceAfter < vaultBalanceBefore;
    assert userBalanceAfter == userBalanceBefore  <=> vaultBalanceAfter == vaultBalanceBefore;


}

// STATE-TRANSITIONS




// RISK-ASSESSMENT

// Property: any rounding error should be in favor of the system (system shoudn't lose)
rule dustFavorsTheHouse(env e, uint assetsIn, address receiver, address owner)
{
    require e.msg.sender != currentContract && receiver != currentContract;
    require totalSupply() != 0;

    uint balanceBefore = ERC20a.balanceOf(currentContract);

    uint shares = deposit(e, assetsIn, receiver);
    uint assetsOut = redeem(e, shares, receiver, owner);

    uint balanceAfter = ERC20a.balanceOf(currentContract);

    assert balanceAfter >= balanceBefore;
}


rule withdrawFrontRunningCheck(env e,env e2,method f,calldataarg arg) {
    safeAssumptions(e);
    safeAssumptions(e2);
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant ERC20aTotalSupplyIsSumOfBalances();
    requireInvariant ERC20bTotalSupplyIsSumOfBalances();
    requireInvariant totalSupplyAlwaysLessThanOrEqualTotalAssets();

    uint assets; 
    storage init = lastStorage;
    withdraw@withrevert(e,assets,e.msg.sender,e.msg.sender);
    bool withdrawReverted = lastReverted;

    f(e2,arg) at init;

    withdraw@withrevert(e,assets,e.msg.sender,e.msg.sender);

    assert !withdrawReverted => !lastReverted;
}












// last revert rule
// Property: if a deposit fails, the user's balance should not change
rule depositRevertsIfNoSharesMinted(env e) {
    uint256 assets; address receiver;
    uint256 sharesBefore = balanceOf(receiver); 

    require asset() != currentContract;

    deposit@withrevert(e, assets, receiver);
    bool isReverted = lastReverted;

    uint256 sharesAfter = balanceOf(receiver);

    assert sharesBefore == sharesAfter <=> isReverted, "Remember, with great power comes great responsibility.";
}