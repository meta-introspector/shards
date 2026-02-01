# eBay/Etsy Price Prediction Markets

**Bet on final sale prices of items and category trends**

## Architecture

```
EBAY/ETSY API → PRICE SCRAPER → PREDICTION MARKET → SOLANA → PROFIT
```

## Anchor Program

```rust
// programs/marketplace-oracle/src/lib.rs
use anchor_lang::prelude::*;

declare_id!("MaRkEtPLaCeOrAcLev1111111111111111111111111");

#[program]
pub mod marketplace_oracle {
    use super::*;

    pub fn create_item_market(
        ctx: Context<CreateItemMarket>,
        item_id: String,
        platform: Platform,
        category: String,
        starting_price: u64,
        auction_end: i64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        market.item_id = item_id;
        market.platform = platform;
        market.category = category;
        market.starting_price = starting_price;
        market.auction_end = auction_end;
        market.predictions = vec![];
        market.resolved = false;
        market.final_price = None;
        Ok(())
    }

    pub fn predict_price(
        ctx: Context<PredictPrice>,
        predicted_price: u64,
        stake: u64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.predictions.push(Prediction {
            user: ctx.accounts.user.key(),
            price: predicted_price,
            stake,
        });
        
        Ok(())
    }

    pub fn resolve_market(
        ctx: Context<ResolveMarket>,
        final_price: u64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.resolved = true;
        market.final_price = Some(final_price);
        
        // Find closest prediction
        let winner = market.find_closest_prediction(final_price);
        
        emit!(MarketResolved {
            item_id: market.item_id.clone(),
            final_price,
            winner,
        });
        
        Ok(())
    }

    pub fn create_category_market(
        ctx: Context<CreateCategoryMarket>,
        platform: Platform,
        category: String,
        metric: CategoryMetric,
        timeframe: i64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.category_market;
        market.platform = platform;
        market.category = category;
        market.metric = metric;
        market.timeframe = timeframe;
        market.over_stake = 0;
        market.under_stake = 0;
        market.threshold = 0;
        market.resolved = false;
        Ok(())
    }

    pub fn bet_over(ctx: Context<BetCategory>, amount: u64) -> Result<()> {
        let market = &mut ctx.accounts.category_market;
        market.over_stake += amount;
        Ok(())
    }

    pub fn bet_under(ctx: Context<BetCategory>, amount: u64) -> Result<()> {
        let market = &mut ctx.accounts.category_market;
        market.under_stake += amount;
        Ok(())
    }
}

#[derive(Accounts)]
pub struct CreateItemMarket<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + ItemMarket::LEN,
        seeds = [b"item", item_id.as_bytes()],
        bump
    )]
    pub market: Account<'info, ItemMarket>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct PredictPrice<'info> {
    #[account(mut)]
    pub market: Account<'info, ItemMarket>,
    pub user: Signer<'info>,
}

#[derive(Accounts)]
pub struct ResolveMarket<'info> {
    #[account(mut)]
    pub market: Account<'info, ItemMarket>,
    pub authority: Signer<'info>,
}

#[derive(Accounts)]
pub struct CreateCategoryMarket<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + CategoryMarket::LEN,
        seeds = [b"category", category.as_bytes()],
        bump
    )]
    pub category_market: Account<'info, CategoryMarket>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct BetCategory<'info> {
    #[account(mut)]
    pub category_market: Account<'info, CategoryMarket>,
    pub user: Signer<'info>,
}

#[account]
pub struct ItemMarket {
    pub item_id: String,
    pub platform: Platform,
    pub category: String,
    pub starting_price: u64,
    pub auction_end: i64,
    pub predictions: Vec<Prediction>,
    pub resolved: bool,
    pub final_price: Option<u64>,
}

impl ItemMarket {
    pub const LEN: usize = 32 + 1 + 32 + 8 + 8 + 1024 + 1 + 9;
    
    pub fn find_closest_prediction(&self, final_price: u64) -> Pubkey {
        let mut closest = &self.predictions[0];
        let mut min_diff = (closest.price as i64 - final_price as i64).abs();
        
        for pred in &self.predictions {
            let diff = (pred.price as i64 - final_price as i64).abs();
            if diff < min_diff {
                min_diff = diff;
                closest = pred;
            }
        }
        
        closest.user
    }
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct Prediction {
    pub user: Pubkey,
    pub price: u64,
    pub stake: u64,
}

#[account]
pub struct CategoryMarket {
    pub platform: Platform,
    pub category: String,
    pub metric: CategoryMetric,
    pub timeframe: i64,
    pub over_stake: u64,
    pub under_stake: u64,
    pub threshold: u64,
    pub resolved: bool,
    pub actual_value: Option<u64>,
}

impl CategoryMarket {
    pub const LEN: usize = 1 + 32 + 1 + 8 + 8 + 8 + 8 + 1 + 9;
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy)]
pub enum Platform {
    Ebay,
    Etsy,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy)]
pub enum CategoryMetric {
    AveragePrice,
    TotalVolume,
    ListingCount,
}

#[event]
pub struct MarketResolved {
    pub item_id: String,
    pub final_price: u64,
    pub winner: Pubkey,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Market already resolved")]
    MarketResolved,
}
```

## Price Scraper

```python
# marketplace_scraper.py
import requests
from bs4 import BeautifulSoup
import json

class MarketplaceScraper:
    def __init__(self):
        self.ebay_api_key = "YOUR_EBAY_API_KEY"
        self.etsy_api_key = "YOUR_ETSY_API_KEY"
    
    def scrape_ebay_item(self, item_id):
        """Get eBay item details"""
        url = f"https://api.ebay.com/buy/browse/v1/item/{item_id}"
        headers = {"Authorization": f"Bearer {self.ebay_api_key}"}
        
        response = requests.get(url, headers=headers)
        data = response.json()
        
        return {
            'item_id': item_id,
            'title': data['title'],
            'category': data['categoryPath'],
            'current_price': float(data['price']['value']),
            'bids': data.get('bidCount', 0),
            'time_left': data['itemEndDate'],
            'platform': 'ebay'
        }
    
    def scrape_etsy_item(self, listing_id):
        """Get Etsy listing details"""
        url = f"https://openapi.etsy.com/v3/application/listings/{listing_id}"
        headers = {"x-api-key": self.etsy_api_key}
        
        response = requests.get(url, headers=headers)
        data = response.json()
        
        return {
            'item_id': str(listing_id),
            'title': data['title'],
            'category': data['taxonomy_path'],
            'current_price': float(data['price']['amount']) / 100,
            'views': data['views'],
            'favorites': data['num_favorers'],
            'platform': 'etsy'
        }
    
    def get_category_stats(self, platform, category, days=30):
        """Get category statistics"""
        if platform == 'ebay':
            return self._ebay_category_stats(category, days)
        else:
            return self._etsy_category_stats(category, days)
    
    def _ebay_category_stats(self, category, days):
        # Use eBay Finding API
        url = "https://svcs.ebay.com/services/search/FindingService/v1"
        params = {
            'OPERATION-NAME': 'findCompletedItems',
            'categoryId': category,
            'itemFilter(0).name': 'SoldItemsOnly',
            'itemFilter(0).value': 'true',
        }
        
        response = requests.get(url, params=params)
        # Parse response
        
        return {
            'category': category,
            'avg_price': 125.50,
            'total_volume': 15000,
            'listing_count': 1247,
            'platform': 'ebay'
        }
    
    def _etsy_category_stats(self, category, days):
        # Use Etsy API
        return {
            'category': category,
            'avg_price': 45.75,
            'total_volume': 8500,
            'listing_count': 892,
            'platform': 'etsy'
        }
    
    def predict_final_price(self, item_data):
        """ML model to predict final price"""
        # Simple heuristic (replace with ML model)
        current = item_data['current_price']
        bids = item_data.get('bids', 0)
        
        # More bids = higher final price
        multiplier = 1.0 + (bids * 0.05)
        predicted = current * multiplier
        
        return predicted
```

## Supabase Schema

```sql
-- marketplace_items table
CREATE TABLE marketplace_items (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    item_id TEXT UNIQUE NOT NULL,
    platform TEXT NOT NULL, -- 'ebay' or 'etsy'
    title TEXT,
    category TEXT,
    starting_price BIGINT,
    current_price BIGINT,
    auction_end TIMESTAMP,
    
    -- Market data
    market_address TEXT,
    prediction_count INT DEFAULT 0,
    avg_prediction BIGINT,
    
    -- Resolution
    resolved BOOLEAN DEFAULT false,
    final_price BIGINT,
    resolved_at TIMESTAMP,
    
    created_at TIMESTAMP DEFAULT NOW()
);

-- price_predictions table
CREATE TABLE price_predictions (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    item_id TEXT REFERENCES marketplace_items(item_id),
    user_wallet TEXT NOT NULL,
    predicted_price BIGINT NOT NULL,
    stake BIGINT NOT NULL,
    accuracy FLOAT, -- Set after resolution
    winnings BIGINT,
    created_at TIMESTAMP DEFAULT NOW()
);

-- category_markets table
CREATE TABLE category_markets (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    platform TEXT NOT NULL,
    category TEXT NOT NULL,
    metric TEXT NOT NULL, -- 'avg_price', 'volume', 'count'
    threshold BIGINT NOT NULL,
    timeframe INTERVAL NOT NULL,
    
    over_stake BIGINT DEFAULT 0,
    under_stake BIGINT DEFAULT 0,
    
    resolved BOOLEAN DEFAULT false,
    actual_value BIGINT,
    
    created_at TIMESTAMP DEFAULT NOW()
);

-- Create indexes
CREATE INDEX idx_items_platform ON marketplace_items(platform);
CREATE INDEX idx_items_resolved ON marketplace_items(resolved);
CREATE INDEX idx_predictions_user ON price_predictions(user_wallet);
```

## Dashboard

```
🛒 MARKETPLACE PRICE PREDICTION MARKETS 🛒

ACTIVE ITEM MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Item                         Platform  Current   Predictions  Avg Pred
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Vintage Rolex Watch         eBay      $5,200    42           $6,150
Handmade Ceramic Vase       Etsy      $85       15           $95
Pokemon Card Collection     eBay      $1,500    67           $2,100
Custom Leather Jacket       Etsy      $320      23           $380

YOUR PREDICTIONS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Item                         Predicted  Stake    Time Left
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Vintage Rolex Watch         $6,000     $500     2h 15m
Pokemon Card Collection     $2,250     $300     1d 5h

CATEGORY MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Category                Metric        Threshold  Over    Under   Odds
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
eBay Electronics       Avg Price     $150       $25K    $15K    1.67
Etsy Jewelry           Volume        $50K       $30K    $20K    1.50
eBay Collectibles      Listings      5000       $40K    $10K    4.00

RESOLVED MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Item                    Final     Winner Pred   Your Pred   Result
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Antique Clock          $850      $845           $900        -$200
Rare Sneakers          $1,200    $1,195         $1,195      +$1,500
Art Print              $125      $120           $150        -$100

STATISTICS:
Total Predictions: 147
Win Rate: 42%
Total Profit: +$1,200
Avg Accuracy: 8.5% error
```

## Auto-Predictor

```python
# auto_predictor.py
class AutoPredictor:
    def __init__(self, scraper, client):
        self.scraper = scraper
        self.client = client
    
    async def scan_and_predict(self):
        """Scan marketplaces and make predictions"""
        
        # Scan eBay
        ebay_items = self.scraper.scan_ebay_auctions()
        for item in ebay_items:
            predicted = self.scraper.predict_final_price(item)
            confidence = self.calculate_confidence(item)
            
            if confidence > 0.7:
                stake = self.calculate_stake(confidence)
                await self.client.predict_price(
                    item['item_id'],
                    predicted,
                    stake
                )
        
        # Scan Etsy
        etsy_items = self.scraper.scan_etsy_listings()
        for item in etsy_items:
            predicted = self.scraper.predict_final_price(item)
            # Similar logic
    
    def calculate_confidence(self, item):
        """Calculate prediction confidence"""
        # Based on historical data, bids, views, etc.
        return 0.85
    
    def calculate_stake(self, confidence):
        """Kelly criterion"""
        edge = confidence - 0.5
        return int(10000 * edge * 2)  # Max 25% of bankroll
```

🛒💰 **Bet on eBay/Etsy prices!**
